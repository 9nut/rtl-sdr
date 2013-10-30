/*
 * rtl-sdr, turns your Realtek RTL2832 based DVB dongle into a SDR receiver
 * Copyright (C) 2012 by Steve Markgraf <steve@steve-m.de>
 * Copyright (C) 2012 by Hoernchen <la@tfc-server.de>
 * Copyright (C) 2012 by Kyle Keen <keenerd@gmail.com>
 * Copyright (C) 2013 by Elias Oenal <EliasOenal@gmail.com>
 * Copyright (C) 2013 by Andreas Reinhardt <info at areinhardt.de>
 *                    with ACARS decoding code by Thierry Leconte (F4DWV)
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */
 
#include <errno.h>
#include <signal.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <math.h>

#ifndef _WIN32
	#include <unistd.h>
#else
	#include <Windows.h>
	#include <fcntl.h>
	#include <io.h>
	#include "getopt/getopt.h"
	#define usleep(x) Sleep(x/1000)
	#define round(x) (x > 0.0 ? floor(x + 0.5): ceil(x - 0.5))
#endif

#include <pthread.h>
#include <libusb.h>
#include "rtl-sdr.h"

#define DEFAULT_ASYNC_BUF_NUMBER	32
#define DEFAULT_BUF_LENGTH		(1 * 16384)
#define MAXIMUM_OVERSAMPLE		16
#define MAXIMUM_BUF_LENGTH		(MAXIMUM_OVERSAMPLE * DEFAULT_BUF_LENGTH)
#define AUTO_GAIN			-100

#define Fe 48000.0
#define Freqh 4800.0/Fe*2.0*M_PI
#define Freql 2400.0/Fe*2.0*M_PI
#define BITLEN ((int)Fe/1200)

/* ACARS defines */
#define VFOPLL 0.7e-3
#define BITPLL 0.2
#define SYN 0x16
#define SOH 0x01
#define POLY 0x1021

static struct bstat_s {
	float hsample[BITLEN];
	float lsample[BITLEN];
	float isample[BITLEN];
	float qsample[BITLEN];
	float csample[BITLEN];
	int is;
	int clock;
	float lin;
	float phih,phil;
	float dfh,dfl;
	float pC,ppC;
	int sgI, sgQ;
	float ea;
} bstat[2];

struct mstat_s {
	enum { HEADL, HEADF, BSYNC1, BSYNC2, SYN1, SYN2, SOH1, TXT, CRC1,
		    CRC2, END } state;
	int ind;
	unsigned short crc;
	char txt[243];
} mstat[2];

static pthread_t demod_thread;
static pthread_mutex_t data_ready;  /* locked when no fresh data available */
static pthread_mutex_t data_write;  /* locked when r/w buffer */
static float h[BITLEN];
static int do_exit = 0;
static rtlsdr_dev_t *dev = NULL;
static int lcm_post[17] = {1,1,1,3,1,5,3,7,1,9,5,11,3,13,7,15,1};

struct fm_state {
	int      now_r, now_j;
	int      pre_r, pre_j;
	int      prev_index;
	int      downsample;    /* min 1, max 256 */
	int      post_downsample;
	int      output_scale;
	uint8_t  buf[MAXIMUM_BUF_LENGTH];
	uint32_t buf_len;
	int      signal[MAXIMUM_BUF_LENGTH];  /* 16 bit signed i/q pairs */
	int16_t  signal2[MAXIMUM_BUF_LENGTH]; /* signal has lowpass, signal2 has demod */
	int      signal_len;
	int      signal2_len;
	int      edge;
	uint32_t freqs[1000];
	int      freq_len;
	int      freq_now;
	uint32_t sample_rate;
	int      output_rate;
	int      now_lpr;
	int      prev_lpr_index;
};

typedef struct {
	unsigned char mode;
	unsigned char addr[8];
	unsigned char ack;
	unsigned char label[3];
	unsigned char bid;
	unsigned char no[5];
	unsigned char fid[7];
	char txt[256];
} msg_t;

// ACARS decoder variables
static long rx_idx;
int c;
msg_t msgl;
unsigned char rl;
int nbitl = 0;
int nrbitl = 8;

void usage(void) {
	fprintf(stderr,
		"rtl_acars, a simple ACARS decoder for RTL2832 based DVB-T receivers\n\n"
		"Use:\trtl_acars -f freq [-options]\n"
		"\t-f frequency_to_tune_to [Hz]\n"
		"\t[-d device_index (default: 0)]\n"
		"\t[-g tuner_gain (default: automatic)]\n"
		"\t[-o oversampling (default: 1)]\n"
		"\t[-p ppm_error (default: 0)]\n"
		"\t[-E sets lower edge tuning (default: center)]\n");
		exit(1);
}

#ifdef _WIN32
BOOL WINAPI
sighandler(int signum) {
	if (CTRL_C_EVENT == signum) {
		fprintf(stderr, "Signal %d caught, exiting!\n",signum);
		do_exit = 1;
		rtlsdr_cancel_async(dev);
		return TRUE;
	}
	return FALSE;
}
#else
static void sighandler(int signum) {
	fprintf(stderr, "Signal %d caught, exiting!\n",signum);
	do_exit = 1;
	rtlsdr_cancel_async(dev);
}
#endif

int getbit(short sample, unsigned char *outbits, int ch) {
	int i, bt;
	float in, in2;
	float C;
	float I, Q;
	float oscl, osch;
	struct bstat_s *st;

	bt = 0;
	st = &bstat[ch];

	in = (float) sample;
	st->lin = 0.003 * fabs(in) + 0.997 * st->lin;
	in /= st->lin;
	in2 = in * in;

	st->is--;
	if (st->is < 0)
		st->is = BITLEN - 1;

	/* VFOs */
	st->phih += Freqh - VFOPLL * st->dfh;
	if (st->phih >= 4.0 * M_PI)
		st->phih -= 4.0 * M_PI;
	st->hsample[st->is] = in2 * sin(st->phih);
	for (i = 0, st->dfh = 0.0; i < BITLEN / 2; i++) {
		st->dfh += st->hsample[(st->is + i) % BITLEN];
	}
	osch = cos(st->phih / 2.0);

	st->phil += Freql - VFOPLL * st->dfl;
	if (st->phil >= 4.0 * M_PI)
		st->phil -= 4.0 * M_PI;
	st->lsample[st->is] = in2 * sin(st->phil);
	for (i = 0, st->dfl = 0.0; i < BITLEN / 2; i++) {
		st->dfl += st->lsample[(st->is + i) % BITLEN];
	}
	oscl = cos(st->phil / 2.0);

	/* mix */
	st->isample[st->is] = in * (oscl + osch);
	st->qsample[st->is] = in * (oscl - osch);
	st->csample[st->is] = oscl * osch;


	/* bit clock */
	st->clock++;
	if (st->clock >= BITLEN/4 + st->ea) {
		st->clock = 0;

		/*  clock filter  */
		for (i = 0, C = 0.0; i < BITLEN; i++) {
			C += h[i] * st->csample[(st->is + i) % BITLEN];
		}

		if (st->pC < C && st->pC < st->ppC) {

			/* integrator */
			for (i = 0, Q = 0.0; i < BITLEN; i++) {
				Q += st->qsample[(st->is + i) % BITLEN];
			}

			if (st->sgQ == 0) {
				if (Q < 0)
					st->sgQ = -1;
				else
					st->sgQ = 1;
			}

			*outbits =
			    ((*outbits) >> 1) | (unsigned
						 char) ((Q * st->sgQ >
							 0) ? 0x80 : 0);
			bt = 1;

			st->ea = -BITPLL * (C - st->ppC);
			if(st->ea > 2.0) st->ea=2.0;
			if(st->ea < -2.0) st->ea=-2.0;
		}
		if (st->pC > C && st->pC > st->ppC) {

			/* integrator */
			for (i = 0, I = 0.0; i < BITLEN; i++) {
				I += st->isample[(st->is + i) % BITLEN];
			}

			if (st->sgI == 0) {
				if (I < 0)
					st->sgI = -1;
				else
					st->sgI = 1;
			}

			*outbits =
			    ((*outbits) >> 1) | (unsigned
						 char) ((I * st->sgI >
							 0) ? 0x80 : 0);
			bt = 1;

			st->ea = BITPLL * (C - st->ppC);
			if(st->ea > 2.0) st->ea=2.0;
			if(st->ea < -2.0) st->ea=-2.0;
		}
		st->ppC = st->pC;
		st->pC = C;
	}
	return bt;
}

void init_bits(void) {
	int i;
	for (i = 0; i < BITLEN; i++)
		h[i] = sin(2.0 * M_PI * (float) i / (float) BITLEN);

	for (i = 0; i < BITLEN; i++) {
		bstat[0].hsample[i] = bstat[0].lsample[i] =
		    bstat[0].isample[i] = bstat[0].qsample[i] =
		    bstat[0].csample[i] = 0.0;
		bstat[1].hsample[i] = bstat[1].lsample[i] =
		    bstat[1].isample[i] = bstat[1].qsample[i] =
		    bstat[1].csample[i] = 0.0;
	}
	bstat[0].is = bstat[0].clock = bstat[0].sgI = bstat[0].sgQ = 0;
	bstat[1].is = bstat[1].clock = bstat[1].sgI = bstat[1].sgQ = 0;
	bstat[0].phih = bstat[0].phil = bstat[0].dfh = bstat[0].dfl =
	    bstat[0].pC = bstat[0].ppC = bstat[0].ea = 0.0;
	bstat[1].phih = bstat[1].phil = bstat[1].dfh = bstat[1].dfl =
	    bstat[1].pC = bstat[1].ppC = bstat[1].ea = 0.0;
	bstat[0].lin=bstat[1].lin=1.0;

}

void init_mesg(void) {
	mstat[0].state = mstat[1].state = HEADL;
}

void resetbits(int ch) {
	bstat[ch].sgI = bstat[ch].sgQ = 0;
}

ssize_t getline(char **linep, size_t *np, FILE *stream) {
  char *p = NULL;
  size_t i = 0;

  if (!linep || !np) {
    errno = EINVAL;
    return -1;
  }

  if (!(*linep) || !(*np)) {
    *np = 120;
    *linep = (char *)malloc(*np);
    if (!(*linep)) {
      return -1;
    }
  }

  flockfile(stream);

  p = *linep;
  int ch;
  for (ch = 0; (ch = getc_unlocked(stream)) != EOF;) {
    if (i > *np) {
      /* Grow *linep. */
      size_t m = *np * 2;
      char *s = (char *)realloc(*linep, m);

      if (!s) {
        int error = errno;
        funlockfile(stream);
        errno = error;
        return -1;
      }

      *linep = s;
      *np = m;
    }

    p[i] = ch;
    if ('\n' == ch) break;
    i += 1;
  }
  funlockfile(stream);

  /* Null-terminate the string. */
  if (i > *np) {
    /* Grow *linep. */
      size_t m = *np * 2;
      char *s = (char *)realloc(*linep, m);

      if (!s) {
        return -1;
      }

      *linep = s;
      *np = m;
  }

  p[i + 1] = '\0';
  return ((i > 0)? (ssize_t) i : -1);
}

static void update_crc(unsigned short *crc, unsigned char ch) {
	unsigned char v;
	unsigned int i;
	unsigned short flag;

	v = 1;
	for (i = 0; i < 8; i++) {
		flag = (*crc & 0x8000);
		*crc = *crc << 1;

		if (ch & v)
			*crc = *crc + 1;

		if (flag != 0)
			*crc = *crc ^ POLY;

		v = v << 1;
	}
}

static int build_mesg(char *txt, int len, msg_t * msg) {
	int i, k;
	char r;

	/* remove special chars */
	for (i = 0; i < len; i++) {
		r = txt[i];
		if (r < ' ' && r != 0x0d && r != 0x0a)
			r = '.'; // was 0xa4 AR CHANGE: Set other placeholder
		txt[i] = r;
	}
	txt[i] = '\0';

	/* fill msg struct */
	k = 0;
	msg->mode = txt[k];
	k++;

	for (i = 0; i < 7; i++, k++) {
		msg->addr[i] = txt[k];
	}
	msg->addr[7] = '\0';

	/* ACK/NAK */
	msg->ack = txt[k];
	k++;

	msg->label[0] = txt[k];
	k++;
	msg->label[1] = txt[k];
	k++;
	msg->label[2] = '\0';

	msg->bid = txt[k];
	k++;

	k++;

	for (i = 0; i < 4; i++, k++) {
		msg->no[i] = txt[k];
	}
	msg->no[4] = '\0';

	for (i = 0; i < 6; i++, k++) {
		msg->fid[i] = txt[k];
	}
	msg->fid[6] = '\0';

	strcpy(msg->txt, &(txt[k]));

	return 1;
}

int getmesg(unsigned char r, msg_t * msg, int ch) {
	struct mstat_s *st;
	st = &(mstat[ch]);

	do {
		switch (st->state) {
		case HEADL:
			if (r == 0xff) {
				st->state = HEADF;
				return 8;
			}
			resetbits(ch);
			return 8;
			break;
		case HEADF:
			if (r != 0xff) {
				int i;
				unsigned char m;

				for (i = 0, m = 1; i < 7; i++, m = m << 1) {
					if (!(r & m))
						break;
				}
				if (i < 2) {
					st->state = HEADL;
					break;
				}
				st->state = BSYNC1;
				st->ind = 0;
				if (i != 2)
					return (i - 2);
				break;
			}
			return 6;
		case BSYNC1:
			if (r != 0x80 + '+')
				st->ind++;
			st->state = BSYNC2;
			return 8;
		case BSYNC2:
			if (r != '*')
				st->ind++;
			st->state = SYN1;
			return 8;
		case SYN1:
			if (r != SYN)
				st->ind++;
			st->state = SYN2;
			return 8;
		case SYN2:
			if (r != SYN)
				st->ind++;
			st->state = SOH1;
			return 8;
		case SOH1:
			if (r != SOH)
				st->ind++;
			if (st->ind > 2) {
				st->state = HEADL;
				break;
			}
			st->state = TXT;
			st->ind = 0;
			st->crc = 0;
			return 8;
		case TXT:
			update_crc(&st->crc, r);
			r = r & 0x7f;
			if (r == 0x03 || r == 0x17) {
				st->state = CRC1;
				return 8;
			}
			st->txt[st->ind] = r;
			st->ind++;
			if (st->ind > 243) {
				st->state = HEADL;
				break;
			}
			return 8;
		case CRC1:
			update_crc(&st->crc, r);
			st->state = CRC2;
			return 8;
		case CRC2:
			update_crc(&st->crc, r);
			st->state = END;
			return 8;
		case END:
			st->state = HEADL;
			if (st->crc == 0) {
				build_mesg(st->txt, st->ind, msg);
				return 0;
			}
			return 8;
		}
	} while (1);
}

/* convert ACARS position reports to APRS position */
static void toaprs(int la, char lac, int ln, char lnc, int prec, char *out) {
    int lad, lnd;
    float lam, lnm;

    lad = la / 10000;
    lnd = ln / 10000;
    lam = (float) (la - (lad * 10000)) * 60.0 / 10000.0;
    lnm = (float) (ln - (lnd * 10000)) * 60.0 / 10000.0;

    switch (prec) {
	case 0:
    		sprintf(out, "%02d%02.0f.  %c/%03d%02.0f.  %c^", lad, lam, lac, lnd, lnm, lnc);
		break;
	case 1:
    		sprintf(out, "%02d%04.1f %c/%03d%04.1f %c^", lad, lam, lac, lnd, lnm, lnc);
		break;
	case 2:
	default:
    		sprintf(out, "%02d%05.2f%c/%03d%05.2f%c^", lad, lam, lac, lnd, lnm, lnc);
		break;
    }
}

int posconv(char *txt, char *pos) {
    char lac, lnc;
    int la, ln;
    char las[7], lns[7];
    int n;
    char *p;

/*try different heuristics */

    n = sscanf(txt, "#M1BPOS%c%05d%c%063d,", &lac, &la, &lnc, &ln);
    if (n == 4 && (lac == 'N' || lac == 'S') && (lnc == 'E' || lnc == 'W')) {
		la *= 10;
		ln *= 10;
		toaprs(la, lac, ln, lnc, 1, pos);
		return 0;;
    }
    n = sscanf(txt, "#M1AAEP%c%06d%c%07d", &lac, &la, &lnc, &ln);
    if (n == 4 && (lac == 'N' || lac == 'S') && (lnc == 'E' || lnc == 'W')) {
		toaprs(la, lac, ln, lnc, 2, pos);
		return 0;;
    }

    if (strncmp(txt, "#M1B", 4) == 0) {
	if ((p = strstr(txt, "/FPO")) != NULL) {
	    n = sscanf(p, "/FPO%c%05d%c%06d", &lac, &la, &lnc, &ln);
	    if (n == 4 && (lac == 'N' || lac == 'S') && (lnc == 'E' || lnc == 'W')) {
			la *= 10;
			ln *= 10;
			toaprs(la, lac, ln, lnc, 1, pos);
			return 0;;
			}
		}
		if ((p = strstr(txt, "/PS")) != NULL) {
			n = sscanf(p, "/PS%c%05d%c%06d", &lac, &la, &lnc, &ln);
			if (n == 4 && (lac == 'N' || lac == 'S') && (lnc == 'E' || lnc == 'W')) {
				la *= 10;
				ln *= 10;
				toaprs(la, lac, ln, lnc, 1, pos);
				return 0;;
			}
		}
    }

    n = sscanf(txt, "FST01%*8s%c%06d%c%07d", &lac, &la, &lnc, &ln);
    if (n == 4 && (lac == 'N' || lac == 'S') && (lnc == 'E' || lnc == 'W')) {
		toaprs(la, lac, ln, lnc, 2, pos);
		return 0;;
    }

    n = sscanf(txt, "(2%c%5c%c%6c", &lac, las, &lnc, lns);
    if (n == 4 && (lac == 'N' || lac == 'S') && (lnc == 'E' || lnc == 'W')) {
		las[5] = 0;
		lns[6] = 0;
		la = 10 * atoi(las);
		ln = 10 * atoi(lns);
		toaprs(la, lac, ln, lnc, 1, pos);
		return 0;;
    }

    n = sscanf(txt, "(:2%c%5c%c%6c", &lac, las, &lnc, lns);
    if (n == 4 && (lac == 'N' || lac == 'S') && (lnc == 'E' || lnc == 'W')) {
		las[5] = 0;
		lns[6] = 0;
		la = 10 * atoi(las);
		ln = 10 * atoi(lns);
		toaprs(la, lac, ln, lnc, 1, pos);
		return 0;;
	}


    n = sscanf(txt, "(2%*4s%c%5c%c%6c", &lac, las, &lnc, lns);
    if (n == 4 && (lac == 'N' || lac == 'S') && (lnc == 'E' || lnc == 'W')) {
		las[5] = 0;
		lns[6] = 0;
		la = 10 * atoi(las);
		ln = 10 * atoi(lns);
		toaprs(la, lac, ln, lnc, 1, pos);
		return 0;;
    }

    n = sscanf(txt, "LAT %c%3c.%3c/LON %c%3c.%3c", &lac, las, &(las[3]),
	       &lnc, lns, &(lns[3]));
    if (n == 6 && (lac == 'N' || lac == 'S') && (lnc == 'E' || lnc == 'W')) {
		las[6] = 0;
		lns[6] = 0;
		la = 10 * atoi(las);
		ln = 10 * atoi(lns);
		toaprs(la, lac, ln, lnc, 1, pos);
		return 0;;
    }

    n = sscanf(txt, "#DFB(POS-%*6s-%04d%c%05d%c/", &la, &lac, &ln, &lnc);
    if (n == 4 && (lac == 'N' || lac == 'S') && (lnc == 'E' || lnc == 'W')) {
		la *= 100;
		ln *= 100;
		toaprs(la, lac, ln, lnc, 0, pos);
		return 0;;
    }

    n = sscanf(txt, "#DFB*POS\a%*8s%c%04d%c%05d/", &lac, &la, &lnc, &ln);
    if (n == 4 && (lac == 'N' || lac == 'S') && (lnc == 'E' || lnc == 'W')) {
		la *= 100;
		ln *= 100;
		toaprs(la, lac, ln, lnc, 0, pos);
		return 0;;
    }

    n = sscanf(txt, "POS%c%05d%c%06d,", &lac, &la, &lnc, &ln);
    if (n == 4 && (lac == 'N' || lac == 'S') && (lnc == 'E' || lnc == 'W')) {
		la *= 10;
		ln *= 10;
		toaprs(la, lac, ln, lnc, 1, pos);
		return 0;;
    }

    n = sscanf(txt, "POS%*2s,%c%05d%c%06d,", &lac, &la, &lnc, &ln);
    if (n == 4 && (lac == 'N' || lac == 'S') && (lnc == 'E' || lnc == 'W')) {
		la *= 10;
		ln *= 10;
		toaprs(la, lac, ln, lnc, 1, pos);
		return 0;;
    }

    n = sscanf(txt, "RCL%*2s,%c%05d%c%06d,", &lac, &la, &lnc, &ln);
    if (n == 4 && (lac == 'N' || lac == 'S') && (lnc == 'E' || lnc == 'W')) {
		la *= 10;
		ln *= 10;
		toaprs(la, lac, ln, lnc, 1, pos);
		return 0;;
    }

    n = sscanf(txt, "TWX%*2s,%c%05d%c%06d,", &lac, &la, &lnc, &ln);
    if (n == 4 && (lac == 'N' || lac == 'S') && (lnc == 'E' || lnc == 'W')) {
		la *= 10;
		ln *= 10;
		toaprs(la, lac, ln, lnc, 1, pos);
		return 0;;
    }

    n = sscanf(txt, "CLA%*2s,%c%05d%c%06d,", &lac, &la, &lnc, &ln);
    if (n == 4 && (lac == 'N' || lac == 'S') && (lnc == 'E' || lnc == 'W')) {
		la *= 10;
		ln *= 10;
		toaprs(la, lac, ln, lnc, 1, pos);
		return 0;;
    }

    n = sscanf(txt, "%c%05d/%c%06d,", &lac, &la, &lnc, &ln);
    if (n == 4 && (lac == 'N' || lac == 'S') && (lnc == 'E' || lnc == 'W')) {
		la *= 10;
		ln *= 10;
		toaprs(la, lac, ln, lnc, 1, pos);
		return 0;;
    }

    return 1;
}

void print_mesg(msg_t * msg) {
	time_t t;
	struct tm *tmp;
	char pos[128];

	printf("RX_IDX: %ld\n", rx_idx);
	printf("ACARS mode: %c, ", msg->mode);
	printf("message label: %s\n", msg->label);
	printf("Aircraft reg: %s, ", msg->addr);
	printf("flight id: %s\n", msg->fid);
	printf("Block id: %d, ", (int) msg->bid);
	printf(" msg. no: %s\n", msg->no);
	printf("Message content:-\n%s", msg->txt);
	rx_idx++;

    if (posconv(msg->txt, pos)==0)
        printf("\nAPRS : Addr:%s Fid:%s Lbl:%s pos:%s\n", msg->addr, msg->fid,msg->label,pos);
 
	t = time(NULL);
	tmp = gmtime(&t);
	printf
	    ("\n----------------------------------------------------------[%02d/%02d/%04d %02d:%02d]\n\n",
	     tmp->tm_mday, tmp->tm_mon + 1, tmp->tm_year + 1900,
	     tmp->tm_hour, tmp->tm_min);

}

///////// END OF ACARS ROUTINES //////////

void rotate_90(unsigned char *buf, uint32_t len) {
	uint32_t i;
	unsigned char tmp;
	for (i=0; i<len; i+=8) {
		tmp = 255 - buf[i+3];
		buf[i+3] = buf[i+2];
		buf[i+2] = tmp;
		buf[i+4] = 255 - buf[i+4];
		buf[i+5] = 255 - buf[i+5];
		tmp = 255 - buf[i+6];
		buf[i+6] = buf[i+7];
		buf[i+7] = tmp;
	}
}

void low_pass(struct fm_state *fm, unsigned char *buf, uint32_t len) {
	int i=0, i2=0;
	while (i < (int)len) {
		fm->now_r += ((int)buf[i]   - 128);
		fm->now_j += ((int)buf[i+1] - 128);
		i += 2;
		fm->prev_index++;
		if (fm->prev_index < fm->downsample) {
			continue;
		}
		fm->signal[i2]   = fm->now_r * fm->output_scale;
		fm->signal[i2+1] = fm->now_j * fm->output_scale;
		fm->prev_index = 0;
		fm->now_r = 0;
		fm->now_j = 0;
		i2 += 2;
	}
	fm->signal_len = i2;
}

// no wrap around, length must be multiple of step
int low_pass_simple(int16_t *signal2, int len, int step) {
	int i, i2, sum;
	for(i=0; i < len; i+=step) {
		sum = 0;
		for(i2=0; i2<step; i2++) {
			sum += (int)signal2[i + i2];
		}
		//signal2[i/step] = (int16_t)(sum / step);
		signal2[i/step] = (int16_t)(sum);
	}
	signal2[i/step + 1] = signal2[i/step];
	return len / step;
}

void low_pass_real(struct fm_state *fm)
/* simple square window FIR */
// add support for upsampling?
{
	int i=0, i2=0;
	int fast = (int)fm->sample_rate / fm->post_downsample;
	int slow = fm->output_rate;
	while (i < fm->signal2_len) {
		fm->now_lpr += fm->signal2[i];
		i++;
		fm->prev_lpr_index += slow;
		if (fm->prev_lpr_index < fast) {
			continue;
		}
		fm->signal2[i2] = (int16_t)(fm->now_lpr / (fast/slow));
		fm->prev_lpr_index -= fast;
		fm->now_lpr = 0;
		i2 += 1;
	}
	fm->signal2_len = i2;
}

void am_demod(struct fm_state *fm) {
	int i, pcm;
	for (i = 0; i < (fm->signal_len); i += 2) {
		pcm = fm->signal[i] * fm->signal[i];
		pcm += fm->signal[i+1] * fm->signal[i+1];
		fm->signal2[i/2] = (int16_t)sqrt(pcm); 
	}
	fm->signal2_len = fm->signal_len/2;
}

int mad(int *samples, int len, int step)
/* mean average deviation */
{
	int i=0, sum=0, ave=0;
	if (len == 0)
		{return 0;}
	for (i=0; i<len; i+=step) {
		sum += samples[i];
	}
	ave = sum / (len * step);
	sum = 0;
	for (i=0; i<len; i+=step) {
		sum += abs(samples[i] - ave);
	}
	return sum / (len / step);
}

static void optimal_settings(struct fm_state *fm, int freq) {
	int r, capture_freq, capture_rate;
	fm->downsample = (1000000 / fm->sample_rate) + 1;
	fm->freq_now = freq;
	capture_rate = fm->downsample * fm->sample_rate;
	capture_freq = fm->freqs[freq] + capture_rate/4;
	capture_freq += fm->edge * fm->sample_rate / 2;
	fm->output_scale = (1<<15) / (128 * fm->downsample);
	if (fm->output_scale < 1) {
		fm->output_scale = 1;}
	fm->output_scale = 1;
	
	/* Set the frequency */
	r = rtlsdr_set_center_freq(dev, (uint32_t)capture_freq);
	fprintf(stderr, "Oversampling input by: %ix.\n", fm->downsample);
	fprintf(stderr, "Oversampling output by: %ix.\n", fm->post_downsample);
	fprintf(stderr, "Buffer size: %0.2fms\n",
		1000 * 0.5 * lcm_post[fm->post_downsample] * (float)DEFAULT_BUF_LENGTH / (float)capture_rate);
	if (r < 0) {
		fprintf(stderr, "WARNING: Failed to set center freq.\n");}
	else {
		fprintf(stderr, "Tuned to %u Hz.\n", capture_freq);}

	/* Set the sample rate */
	fprintf(stderr, "Sampling at %u Hz.\n", capture_rate);
	if (fm->output_rate > 0) {
		fprintf(stderr, "Output at %u Hz.\n", fm->output_rate);
	} else {
		fprintf(stderr, "Output at %u Hz.\n", fm->sample_rate/fm->post_downsample);}
	r = rtlsdr_set_sample_rate(dev, (uint32_t)capture_rate);
	if (r < 0) {
		fprintf(stderr, "WARNING: Failed to set sample rate.\n");}

}

void full_demod(struct fm_state *fm) {
	rotate_90(fm->buf, fm->buf_len);
	low_pass(fm, fm->buf, fm->buf_len);
	pthread_mutex_unlock(&data_write);
	
	am_demod(fm);

	if (fm->post_downsample > 1) {
		fm->signal2_len = low_pass_simple(fm->signal2, fm->signal2_len, fm->post_downsample);
	}
		
	if (fm->output_rate > 0) {
		low_pass_real(fm);
	}
}

void acars_decode(struct fm_state *fm) {
	int16_t* sample = fm->signal2;
	int ind;	
	for (ind = 0; ind < fm->signal2_len;) {
		nbitl += getbit(sample[ind], &rl, 0);
		if (nbitl >= nrbitl) {
			nrbitl = getmesg(rl, &msgl, 0);
			nbitl = 0;
			if (nrbitl == 0) {
				print_mesg(&msgl);
				memset(&msgl, 0, sizeof(msgl));
				memset(&mstat[0], 0, sizeof(mstat[0]));
				nrbitl = 8;
			}
		}
		ind++;
	}
}

static void rtlsdr_callback(unsigned char *buf, uint32_t len, void *ctx) {
	struct fm_state *fm2 = ctx;
	if (do_exit) return;
	if (!ctx) return;
	pthread_mutex_lock(&data_write);
	memcpy(fm2->buf, buf, len);
	fm2->buf_len = len;
	pthread_mutex_unlock(&data_ready);
}

static void *demod_thread_fn(void *arg) {
	struct fm_state *fm2 = arg;
	while (!do_exit) {
		pthread_mutex_lock(&data_ready);
		full_demod(fm2);
		acars_decode(fm2);
	}
	return 0;
}

double atofs(char* f) {
	char* chop = malloc((strlen(f)+1)*sizeof(char));
	double suff = 1.0;
	strncpy(chop, f, strlen(f)-1);
	
	switch (f[strlen(f)-1]) {
		case 'G':
			suff *= 1e3;
		case 'M':
			suff *= 1e3;
		case 'k':
			suff *= 1e3;
    	suff *= atof(chop);
    }
	free(chop);
	if (suff != 1.0) return suff;
	return atof(f);
}

void fm_init(struct fm_state *fm) {
	fm->freqs[0] = 131550000;
	fm->sample_rate = 48000;
	fm->freq_len = 0;
	fm->edge = 0;
	fm->prev_index = 0;
	fm->post_downsample = 1;  // once this works, default = 4
	fm->output_rate = -1; // disabled
	fm->pre_j = fm->pre_r = fm->now_r = fm->now_j = 0;
	fm->prev_lpr_index = 0;
	fm->now_lpr = 0;
}

int main(int argc, char **argv) {
#ifndef _WIN32
	struct sigaction sigact;
#endif
	struct fm_state fm; 
	int r, opt;
	int i, gain = AUTO_GAIN; // tenths of a dB
	uint8_t *buffer;
	uint32_t dev_index = 0;
	int device_count;
	int ppm_error = 0;
	char vendor[256], product[256], serial[256];
	
	fm_init(&fm);
	pthread_mutex_init(&data_ready, NULL);
	pthread_mutex_init(&data_write, NULL);

	fm.sample_rate = (uint32_t) 48000;

	while ((opt = getopt(argc, argv, "d:f:g:o:p:E:")) != -1) {
		switch (opt) {
		case 'd':
			dev_index = atoi(optarg);
			break;
		case 'f':
			fm.freqs[fm.freq_len] = (uint32_t)atofs(optarg);
			fm.freq_len++;
			break;
		case 'g':
			gain = (int)(atof(optarg) * 10);
			break;
		case 'o':
			fm.post_downsample = (int)atof(optarg);
			if (fm.post_downsample < 1 || fm.post_downsample > MAXIMUM_OVERSAMPLE) {
				fprintf(stderr, "Oversample must be between 1 and %i\n", MAXIMUM_OVERSAMPLE);}
			break;
		case 'p':
			ppm_error = atoi(optarg);
			break;
		case 'E':
			fm.edge = 1;
			break;
		default:
			usage();
			break;
		}
	}

	/* quadruple sample_rate to limit to Δθ to ±π/2 */
	fm.sample_rate *= fm.post_downsample;

	if (fm.freq_len == 0 || fm.freq_len > 1) {
		fprintf(stderr, "Please specify exactly one frequency (or use -h for help).\n");
		exit(1);
	}

	buffer = malloc(lcm_post[fm.post_downsample] * DEFAULT_BUF_LENGTH * sizeof(uint8_t));

	device_count = rtlsdr_get_device_count();
	if (!device_count) {
		fprintf(stderr, "No supported devices found.\n");
		exit(1);
	}

	fprintf(stderr, "Found %d device(s):\n", device_count);
	for (i = 0; i < device_count; i++) {
		rtlsdr_get_device_usb_strings(i, vendor, product, serial);
		fprintf(stderr, "  %d:  %s, %s, SN: %s\n", i, vendor, product, serial);
	}
	fprintf(stderr, "\n");

	init_bits();
	init_mesg();

	fprintf(stderr, "Using device %d: %s\n",
		dev_index, rtlsdr_get_device_name(dev_index));

	r = rtlsdr_open(&dev, dev_index);
	if (r < 0) {
		fprintf(stderr, "Failed to open rtlsdr device #%d.\n", dev_index);
		exit(1);
	}
	
#ifndef _WIN32
	sigact.sa_handler = sighandler;
	sigemptyset(&sigact.sa_mask);
	sigact.sa_flags = 0;
	sigaction(SIGINT, &sigact, NULL);
	sigaction(SIGTERM, &sigact, NULL);
	sigaction(SIGQUIT, &sigact, NULL);
	sigaction(SIGPIPE, &sigact, NULL);
#else
	SetConsoleCtrlHandler( (PHANDLER_ROUTINE) sighandler, TRUE );
#endif

	optimal_settings(&fm, 0);

	/* Set the tuner gain */
	if (gain == AUTO_GAIN) {
		r = rtlsdr_set_tuner_gain_mode(dev, 0);
	} else {
		r = rtlsdr_set_tuner_gain_mode(dev, 1);
		r = rtlsdr_set_tuner_gain(dev, gain);
	}
	if (r != 0) {
		fprintf(stderr, "WARNING: Failed to set tuner gain.\n");
	} else if (gain == AUTO_GAIN) {
		fprintf(stderr, "Tuner gain set to automatic.\n");
	} else {
		fprintf(stderr, "Tuner gain set to %0.2f dB.\n", gain/10.0);
	}
	r = rtlsdr_set_freq_correction(dev, ppm_error);

	/* Reset endpoint before we start reading from it (mandatory) */
	r = rtlsdr_reset_buffer(dev);
	if (r < 0) {
		fprintf(stderr, "WARNING: Failed to reset buffers.\n");
	}

	pthread_create(&demod_thread, NULL, demod_thread_fn, (void *)(&fm));
	rtlsdr_read_async(dev, rtlsdr_callback, (void *)(&fm),
			      DEFAULT_ASYNC_BUF_NUMBER,
			      lcm_post[fm.post_downsample] * DEFAULT_BUF_LENGTH);

	if (do_exit) {
		fprintf(stderr, "\nUser cancel, exiting...\n");
	} else {
		fprintf(stderr, "\nLibrary error %d, exiting...\n", r);
	}
	
	rtlsdr_cancel_async(dev);
	pthread_mutex_destroy(&data_ready);
	pthread_mutex_destroy(&data_write);

	rtlsdr_close(dev);
	free (buffer);
	return r >= 0 ? r : -r;
}
