/*
 * rtl-sdr, turns your Realtek RTL2832 based DVB dongle into a SDR receiver
 * Copyright (C) 2012 by Steve Markgraf <steve@steve-m.de>
 * Copyright (C) 2012 by Hoernchen <la@tfc-server.de>
 * Copyright (C) 2012 by Kyle Keen <keenerd@gmail.com>
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


/*
 * rtl_power: general purpose FFT integrator
 * -f low_freq:high_freq:max_bin_size
 * -i seconds
 * outputs CSV
 * time, low, high, step, db, db, db ...
 * db optional?  raw output might be better for noise correction
 * todo:
 *	threading
 *	randomized hopping
 *	noise correction
 *	continuous IIR
 *	general astronomy usefulness
 *	multiple dongles
 *	multiple FFT workers
 *	fft bins smaller than 61Hz
 *	bandwidths smaller than 1MHz
 *	check edge cropping for off-by-one and rounding errors
 */

#include <errno.h>
#include <signal.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#ifndef _WIN32
#include <unistd.h>
#else
#include <windows.h>
#include <fcntl.h>
#include <io.h>
#include "getopt/getopt.h"
#define usleep(x) Sleep(x/1000)
#define round(x) (x > 0.0 ? floor(x + 0.5): ceil(x - 0.5))
#define _USE_MATH_DEFINES
#endif

#include <math.h>
#include <pthread.h>
#include <libusb.h>

#include "rtl-sdr.h"

#define DEFAULT_SAMPLE_RATE		24000
#define DEFAULT_ASYNC_BUF_NUMBER	32
#define DEFAULT_BUF_LENGTH		(1 * 16384)
#define MAXIMUM_OVERSAMPLE		16
#define MAXIMUM_BUF_LENGTH		(MAXIMUM_OVERSAMPLE * DEFAULT_BUF_LENGTH)
#define AUTO_GAIN			-100
#define BUFFER_DUMP			(1<<12)

static volatile int do_exit = 0;
static rtlsdr_dev_t *dev = NULL;
FILE *file;

int16_t* Sinewave;
double* power_table;
int N_WAVE, LOG2_N_WAVE;
int next_power;
int16_t *fft_buf;
int *window_coefs;

struct tuning_state
/* one per tuning range */
{
	int freq;
	int rate;
	int bin_e;
	long *avg;  /* length == 2^bin_e */
	int samples;
	long mega_samples;
	//pthread_rwlock_t avg_lock;
	//pthread_mutex_t avg_mutex;
	/* having the iq buffer here is wasteful, but will avoid contention */
	uint8_t *buf8;
	int buf_len;
	//pthread_rwlock_t buf_lock;
	//pthread_mutex_t buf_mutex;
};

/* 3000 is enough for 3GHz b/w worst case */
#define MAX_TUNES	3000
struct tuning_state tunes[MAX_TUNES];
int tune_count = 0;

void usage(void)
{
	fprintf(stderr,
		"rtl_power, a simple FFT logger for RTL2832 based DVB-T receivers\n\n"
		"Use:\trtl_power -f freq_range [-options] [filename]\n"
		"\t-f lower:upper:bin_size [Hz]\n"
		"\t (bin size is a maximum, smaller more convenient bins\n"
		"\t  will be used.  valid range 61-2M)\n"
		"\t[-i integration_interval (default: 10 seconds)]\n"
		"\t (buggy if a full sweep takes longer than the interval)\n"
		"\t[-1 enables single-shot mode (default: off)]\n"
		"\t[-e exit_timer (default: off/0)]\n"
		//"\t[-s avg/iir smoothing (default: avg)]\n"
		//"\t[-t threads (default: 1)]\n"
		"\t[-d device_index (default: 0)]\n"
		"\t[-g tuner_gain (default: automatic)]\n"
		"\t[-p ppm_error (default: 0)]\n"
		"\tfilename (a '-' dumps samples to stdout)\n"
		"\t (omitting the filename also uses stdout)\n"
		"\n"
		"Experimental options:\n"
		"\t[-w window (default: rectangle)]\n"
		"\t (hamming, blackman, blackman-harris, hann-poisson, bartlett, youssef)\n"
		// kaiser
		"\t[-c crop_percent (default: 0%, recommended: 20%%-50%%)]\n"
		"\t (discards data at the edges, 100%% discards everything)\n"
		"\t (has no effect in rms bin mode)\n"
		"\n"
		"CSV FFT output columns:\n"
		"\tdate, time, Hz low, Hz high, Hz step, samples, dbm, dbm, ...\n\n"
		"Examples:\n"
		"\trtl_power -f 88M:108M:125k fm_stations.csv\n"
		"\t (creates 160 bins across the FM band,\n"
		"\t  individual stations should be visible)\n"
		"\trtl_power -f 100M:1G:1M -i 5m -1 survey.csv\n"
		"\t (a five minute low res scan of nearly everything)\n"
		"\trtl_power -f ... -i 15m -1 log.csv\n"
		"\t (integrate for 15 minutes and exit afterwards)\n"
		"\trtl_power -f ... -e 1h | gzip > log.csv.gz\n"
		"\t (collect data for one hour and compress it on the fly)\n"
		"Convert CSV to a waterfall graphic with\n"
		"\thttp://kmkeen.com/tmp/heatmap.py.txt\n"
		"");
	exit(1);
}

#ifdef _WIN32
BOOL WINAPI
sighandler(int signum)
{
	if (CTRL_C_EVENT == signum) {
		fprintf(stderr, "Signal caught, exiting!\n");
		do_exit = 1;
		return TRUE;
	}
	return FALSE;
}
#else
static void sighandler(int signum)
{
	fprintf(stderr, "Signal caught, exiting!\n");
	do_exit = 1;
}
#endif

/* more cond dumbness */
#define safe_cond_signal(n, m) pthread_mutex_lock(m); pthread_cond_signal(n); pthread_mutex_unlock(m)
#define safe_cond_wait(n, m) pthread_mutex_lock(m); pthread_cond_wait(n, m); pthread_mutex_unlock(m)

/* FFT based on fix_fft.c by Roberts, Slaney and Bouras
   http://www.jjj.de/fft/fftpage.html
   16 bit ints for everything
   -32768..+32768 maps to -1.0..+1.0
*/

void sine_table(int size)
{
	int i;
	double d;
	LOG2_N_WAVE = size;
	N_WAVE = 1 << LOG2_N_WAVE;
	Sinewave = malloc(sizeof(int16_t) * N_WAVE*3/4);
	power_table = malloc(sizeof(double) * N_WAVE);
	for (i=0; i<N_WAVE*3/4; i++)
	{
		d = (double)i * 2.0 * M_PI / N_WAVE;
		Sinewave[i] = (int)round(32767*sin(d));
		//printf("%i\n", Sinewave[i]);
	}
}

static inline int16_t FIX_MPY(int16_t a, int16_t b)
/* fixed point multiply and scale */
{
	int c = ((int)a * (int)b) >> 14;
	b = c & 0x01;
	return (c >> 1) + b;
}

int fix_fft(int16_t iq[], int16_t m)
/* interleaved iq[], 0 <= n < 2**m, changes in place */
{
	int mr, nn, i, j, l, k, istep, n, shift;
	int16_t qr, qi, tr, ti, wr, wi;
	n = 1 << m;
	if (n > N_WAVE)
		{return -1;}
	mr = 0;
	nn = n - 1;
	/* decimation in time - re-order data */
	for (m=1; m<=nn; ++m) {
		l = n;
		do
			{l >>= 1;}
		while (mr+l > nn);
		mr = (mr & (l-1)) + l;
		if (mr <= m)
			{continue;}
		// real = 2*m, imag = 2*m+1
		tr = iq[2*m];
		iq[2*m] = iq[2*mr];
		iq[2*mr] = tr;
		ti = iq[2*m+1];
		iq[2*m+1] = iq[2*mr+1];
		iq[2*mr+1] = ti;
	}
	l = 1;
	k = LOG2_N_WAVE-1;
	while (l < n) {
		shift = 1;
		istep = l << 1;
		for (m=0; m<l; ++m) {
			j = m << k;
			wr =  Sinewave[j+N_WAVE/4];
			wi = -Sinewave[j];
			if (shift) {
				wr >>= 1; wi >>= 1;}
			for (i=m; i<n; i+=istep) {
				j = i + l;
				tr = FIX_MPY(wr,iq[2*j]) - FIX_MPY(wi,iq[2*j+1]);
				ti = FIX_MPY(wr,iq[2*j+1]) + FIX_MPY(wi,iq[2*j]);
				qr = iq[2*i];
				qi = iq[2*i+1];
				if (shift) {
					qr >>= 1; qi >>= 1;}
				iq[2*j] = qr - tr;
				iq[2*j+1] = qi - ti;
				iq[2*i] = qr + tr;
				iq[2*i+1] = qi + ti;
			}
		}
		--k;
		l = istep;
	}
	return 0;
}

double rectangle(int i, int length)
{
	return 1.0;
}

double hamming(int i, int length)
{
	double a, b, w, N1;
	a = 25.0/46.0;
	b = 21.0/46.0;
	N1 = (double)(length-1);
	w = a - b*cos(2*i*M_PI/N1);
	return w;
}

double blackman(int i, int length)
{
	double a0, a1, a2, w, N1;
	a0 = 7938.0/18608.0;
	a1 = 9240.0/18608.0;
	a2 = 1430.0/18608.0;
	N1 = (double)(length-1);
	w = a0 - a1*cos(2*i*M_PI/N1) + a2*cos(4*i*M_PI/N1);
	return w;
}

double blackman_harris(int i, int length)
{
	double a0, a1, a2, a3, w, N1;
	a0 = 0.35875;
	a1 = 0.48829;
	a2 = 0.14128;
	a3 = 0.01168;
	N1 = (double)(length-1);
	w = a0 - a1*cos(2*i*M_PI/N1) + a2*cos(4*i*M_PI/N1) - a3*cos(6*i*M_PI/N1);
	return w;
}

double hann_poisson(int i, int length)
{
	double a, N1, w;
	a = 2.0;
	N1 = (double)(length-1);
	w = 0.5 * (1 - cos(2*M_PI*i/N1)) * \
	    pow(M_E, (-a*(double)abs((int)(N1-1-2*i)))/N1);
	return w;
}

double youssef(int i, int length)
/* really a blackman-harris-poisson window, but that is a mouthful */
{
	double a, a0, a1, a2, a3, w, N1;
	a0 = 0.35875;
	a1 = 0.48829;
	a2 = 0.14128;
	a3 = 0.01168;
	N1 = (double)(length-1);
	w = a0 - a1*cos(2*i*M_PI/N1) + a2*cos(4*i*M_PI/N1) - a3*cos(6*i*M_PI/N1);
	a = 0.0025;
	w *= pow(M_E, (-a*(double)abs((int)(N1-1-2*i)))/N1);
	return w;
}

double kaiser(int i, int length)
// todo, become more smart
{
	return 1.0;
}

double bartlett(int i, int length)
{
	double N1, L, w;
	L = (double)length;
	N1 = L - 1;
	w = (i - N1/2) / (L/2);
	if (w < 0) {
		w = -w;}
	w = 1 - w;
	return w;
}

void rms_power(struct tuning_state *ts)
/* for bins between 1MHz and 2MHz */
{
	int i, s;
	uint8_t *buf = ts->buf8;
	int buf_len = ts->buf_len;
	long p, t;
	int ln, lp;
	double dc, err;

	p = t = 0L;
	for (i=0; i<buf_len; i++) {
		s = (int)buf[i] - 127;
		t += (long)s;
		p += (long)(s * s);
	}
	/* correct for dc offset in squares */
	dc = (double)t / (double)buf_len;
	err = t * 2 * dc - dc * dc * buf_len;
	p -= (long)round(err);

	ts->avg[0] += p;
	ts->samples += 1;
	/* complex pairs, half length */
	ts->mega_samples += (long)(buf_len/2);
}

double atofs(char *f)
/* standard suffixes */
{
	char last;
	int len;
	double suff = 1.0;
	len = strlen(f);
	last = f[len-1];
	f[len-1] = '\0';
	switch (last) {
		case 'g':
		case 'G':
			suff *= 1e3;
		case 'm':
		case 'M':
			suff *= 1e3;
		case 'k':
		case 'K':
			suff *= 1e3;
			suff *= atof(f);
			f[len-1] = last;
			return suff;
	}
	f[len-1] = last;
	return atof(f);
}

double atoft(char *f)
/* time suffixes */
{
	char last;
	int len;
	double suff = 1.0;
	len = strlen(f);
	last = f[len-1];
	f[len-1] = '\0';
	switch (last) {
		case 'h':
		case 'H':
			suff *= 60;
		case 'm':
		case 'M':
			suff *= 60;
		case 's':
		case 'S':
			suff *= atof(f);
			f[len-1] = last;
			return suff;
	}
	f[len-1] = last;
	return atof(f);
}

double atofp(char *f)
/* percent suffixes */
{
	char last;
	int len;
	double suff = 1.0;
	len = strlen(f);
	last = f[len-1];
	f[len-1] = '\0';
	switch (last) {
		case '%':
			suff *= 0.01;
			suff *= atof(f);
			f[len-1] = last;
			return suff;
	}
	f[len-1] = last;
	return atof(f);
}

int nearest_gain(int target_gain)
{
	int i, err1, err2, count, close_gain;
	int* gains;
	count = rtlsdr_get_tuner_gains(dev, NULL);
	if (count <= 0) {
		return 0;
	}
	gains = malloc(sizeof(int) * count);
	count = rtlsdr_get_tuner_gains(dev, gains);
	close_gain = gains[0];
	for (i=0; i<count; i++) {
		err1 = abs(target_gain - close_gain);
		err2 = abs(target_gain - gains[i]);
		if (err2 < err1) {
			close_gain = gains[i];
		}
	}
	free(gains);
	return close_gain;
}

void frequency_range(char *arg, double crop)
/* flesh out the tunes[] for scanning */
// do we want the fewest ranges (easy) or the fewest bins (harder)?
{
	char *start, *stop, *step;
	int i, j, upper, lower, max_size, bw_seen, bw_used, bin_size, bin_e, buf_len;
	struct tuning_state *ts;
	/* hacky string parsing */
	start = arg;
	stop = strchr(start, ':') + 1;
	stop[-1] = '\0';
	step = strchr(stop, ':') + 1;
	step[-1] = '\0';
	lower = (int)atofs(start);
	upper = (int)atofs(stop);
	max_size = (int)atofs(step);
	stop[-1] = ':';
	step[-1] = ':';
	/* evenly sized ranges, as close to 2MHz as possible */
	for (i=1; i<1500; i++) {
		bw_seen = (upper - lower) / i;
		bw_used = (int)((double)(bw_seen) / (1.0 - crop));
		if (bw_used > 2000000) {
			continue;}
		tune_count = i;
		break;
	}
	/* number of bins is power-of-two, bin size is under limit */
	for (i=1; i<=21; i++) {
		bin_e = i;
		bin_size = bw_used / (1<<i);
		if (bin_size <= max_size) {
			break;}
	}
	/* unless giant bins */
	if (max_size >= 1000000) {
		bw_seen = max_size;
		bw_used = max_size;
		tune_count = (upper - lower) / bw_seen;
		bin_e = 0;
	}
	if (tune_count > MAX_TUNES) {
		fprintf(stderr, "Error: bandwidth too wide.\n");
		exit(1);
	}
	buf_len = DEFAULT_BUF_LENGTH;
	if ((2<<bin_e) > buf_len) {
		buf_len = (2<<bin_e);
	}
	/* build the array */
	for (i=0; i<tune_count; i++) {
		ts = &tunes[i];
		ts->freq = lower + i*bw_seen + bw_seen/2;
		ts->rate = bw_used;
		ts->bin_e = bin_e;
		ts->samples = 0;
		ts->mega_samples = 0L;
		ts->avg = (long*)malloc((1<<bin_e) * sizeof(long));
		if (!ts->avg) {
			fprintf(stderr, "Error: malloc.\n");
			exit(1);
		}
		for (j=0; j<(1<<bin_e); j++) {
			ts->avg[j] = 0L;
		}
		ts->buf8 = (uint8_t*)malloc(buf_len * sizeof(uint8_t));
		if (!ts->buf8) {
			fprintf(stderr, "Error: malloc.\n");
			exit(1);
		}
		ts->buf_len = buf_len;
	}
	/* report */
	fprintf(stderr, "Number of frequency hops: %i\n", tune_count);
	fprintf(stderr, "Dongle bandwidth: %iHz\n", bw_used);
	fprintf(stderr, "Total FFT bins: %i\n", tune_count * (1<<bin_e));
	fprintf(stderr, "Logged FFT bins: %i\n", \
	  (int)((double)(tune_count * (1<<bin_e)) * (1.0-crop)));
	fprintf(stderr, "FFT bin size: %iHz\n", bin_size);
	fprintf(stderr, "Buffer size: %0.2fms\n", 1000 * 0.5 * (float)buf_len / (float)bw_used);
}

void retune(rtlsdr_dev_t *d, int freq)
{
	uint8_t dump[BUFFER_DUMP];
	int n_read;
	rtlsdr_set_center_freq(d, (uint32_t)freq);
	/* wait for settling and flush buffer */
	usleep(5000);
	rtlsdr_read_sync(d, &dump, BUFFER_DUMP, &n_read);
	if (n_read != BUFFER_DUMP) {
		fprintf(stderr, "Error: bad retune.\n");}
}

void scanner(void)
{
	int i, j, f, n_read, offset, bin_e, bin_len, buf_len;
	struct tuning_state *ts;
	bin_e = tunes[0].bin_e;
	bin_len = 1 << bin_e;
	buf_len = tunes[0].buf_len;
	for (i=0; i<tune_count; i++) {
		if (do_exit) {
			break;}
		ts = &tunes[i];
		f = (int)rtlsdr_get_center_freq(dev);
		if (f != ts->freq) {
			retune(dev, ts->freq);}
		rtlsdr_read_sync(dev, ts->buf8, buf_len, &n_read);
		if (n_read != buf_len) {
			fprintf(stderr, "Error: dropped samples.\n");}
		/* rms */
		if (bin_len == 1) {
			rms_power(ts);
			continue;
		}
		/* fft */
		for (j=0; j<buf_len; j++) {
			fft_buf[j] = (int16_t)ts->buf8[j] - 127;
		}
		for (offset=0; offset<buf_len; offset+=(2*bin_len)) {
			// todo, let rect skip this
			for (j=0; j<bin_len; j++) {
				fft_buf[offset+j*2]   *= window_coefs[j];
				fft_buf[offset+j*2+1] *= window_coefs[j];
			}
			fix_fft(fft_buf+offset, bin_e);
			for (j=0; j<bin_len; j++) {
				ts->avg[j] += (long) abs(fft_buf[offset+j*2]);
			}
			ts->samples += 1;
		}
	}
}

void csv_dbm(struct tuning_state *ts, double crop)
{
	int i, len, i1, i2, bw2;
	long tmp;
	double dbm;
	len = 1 << ts->bin_e;
	/* fix FFT stuff quirks */
	if (ts->bin_e > 0) {
		/* nuke DC component (not effective for all windows) */
		ts->avg[0] = ts->avg[1];
		/* FFT is translated by 180 degrees */
		for (i=0; i<len/2; i++) {
			tmp = ts->avg[i];
			ts->avg[i] = ts->avg[i+len/2];
			ts->avg[i+len/2] = tmp;
		}
	}
	/* Hz low, Hz high, Hz step, samples, dbm, dbm, ... */
	bw2 = (int)((double)ts->rate * (1.0-crop) * 0.5);
	fprintf(file, "%i, %i, %.2f, %i, ", ts->freq - bw2, ts->freq + bw2,
		(double)ts->rate / (double)len, ts->samples);
	// something seems off with the dbm math
	i1 = 0 + (int)((double)len * crop * 0.5);
	i2 = (len-1) - (int)((double)len * crop * 0.5);
	for (i=i1; i<i2; i++) {
		dbm  = (double)ts->avg[i];
		dbm /= (double)ts->rate;
		dbm /= (double)ts->samples;
		dbm  = 10 * log10(dbm);
		fprintf(file, "%.2f, ", dbm);
	}
	dbm = (double)ts->avg[i2] / ((double)ts->rate * (double)ts->samples);
	if (ts->bin_e == 0) {
		dbm = ((double)ts->avg[0] / \
		((double)ts->rate * (double)ts->samples));}
	dbm  = 10 * log10(dbm);
	fprintf(file, "%.2f\n", dbm);
	for (i=0; i<len; i++) {
		ts->avg[i] = 0L;
	}
	ts->samples = 0;
	ts->mega_samples = 0L;
}

int main(int argc, char **argv)
{
#ifndef _WIN32
	struct sigaction sigact;
#endif
	char *filename = NULL;
	int i, length, n_read, r, opt, wb_mode = 0;
	int gain = AUTO_GAIN; // tenths of a dB
	uint8_t *buffer;
	uint32_t dev_index = 0;
	int device_count;
	int ppm_error = 0;
	int interval = 10;
	int fft_threads = 1;
	int smoothing = 0;
	int single = 0;
	double crop = 0.1;
	char vendor[256], product[256], serial[256];
	char *freq_optarg;
	time_t next_tick;
	time_t time_now;
	time_t exit_time = 0;
	char t_str[50];
	struct tm *cal_time;
	double (*window_fn)(int, int) = rectangle;

	while ((opt = getopt(argc, argv, "f:i:s:t:d:g:p:e:w:c:1h")) != -1) {
		switch (opt) {
		case 'f': // lower:upper:bin_size
			freq_optarg = strdup(optarg);
			break;
		case 'd':
			dev_index = atoi(optarg);
			break;
		case 'g':
			gain = (int)(atof(optarg) * 10);
			break;
		case 'c':
			crop = atofp(optarg);
			break;
		case 'i':
			interval = (int)round(atoft(optarg));
			break;
		case 'e':
			exit_time = (time_t)((int)round(atoft(optarg)));
			break;
		case 's':
			if (strcmp("avg",  optarg) == 0) {
				smoothing = 0;}
			if (strcmp("iir",  optarg) == 0) {
				smoothing = 1;}
			break;
		case 'w':
			if (strcmp("rectangle",  optarg) == 0) {
				window_fn = rectangle;}
			if (strcmp("hamming",  optarg) == 0) {
				window_fn = hamming;}
			if (strcmp("blackman",  optarg) == 0) {
				window_fn = blackman;}
			if (strcmp("blackman-harris",  optarg) == 0) {
				window_fn = blackman_harris;}
			if (strcmp("hann-poisson",  optarg) == 0) {
				window_fn = hann_poisson;}
			if (strcmp("youssef",  optarg) == 0) {
				window_fn = youssef;}
			if (strcmp("kaiser",  optarg) == 0) {
				window_fn = kaiser;}
			if (strcmp("bartlett",  optarg) == 0) {
				window_fn = bartlett;}
			break;
		case 't':
			fft_threads = atoi(optarg);
			break;
		case 'p':
			ppm_error = atoi(optarg);
			break;
		case '1':
			single = 1;
			break;
		case 'h':
		default:
			usage();
			break;
		}
	}

	frequency_range(freq_optarg, crop);

	if (tune_count == 0) {
		usage();}

	if (argc <= optind) {
		filename = "-";
	} else {
		filename = argv[optind];
	}

	if (interval < 1) {
		interval = 1;}

	fprintf(stderr, "Reporting every %i seconds\n", interval);

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

	/* Set the tuner gain */
	if (gain == AUTO_GAIN) {
		r = rtlsdr_set_tuner_gain_mode(dev, 0);
	} else {
		r = rtlsdr_set_tuner_gain_mode(dev, 1);
		gain = nearest_gain(gain);
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

	if (strcmp(filename, "-") == 0) { /* Write log to stdout */
		file = stdout;
#ifdef _WIN32
		_setmode(_fileno(file), _O_BINARY);
#endif
	} else {
		file = fopen(filename, "wb");
		if (!file) {
			fprintf(stderr, "Failed to open %s\n", filename);
			exit(1);
		}
	}

	/* Reset endpoint before we start reading from it (mandatory) */
	r = rtlsdr_reset_buffer(dev);
	if (r < 0) {
		fprintf(stderr, "WARNING: Failed to reset buffers.\n");}

	/* actually do stuff */
	rtlsdr_set_sample_rate(dev, (uint32_t)tunes[0].rate);
	sine_table(tunes[0].bin_e);
	next_tick = time(NULL) + interval;
	if (exit_time) {
		exit_time = time(NULL) + exit_time;}
	fft_buf = malloc(tunes[0].buf_len * sizeof(int16_t));
	length = 1 << tunes[0].bin_e;
	window_coefs = malloc(length * sizeof(int));
	for (i=0; i<length; i++) {
		window_coefs[i] = (int)(256*window_fn(i, length));
	}
	while (!do_exit) {
		scanner();
		time_now = time(NULL);
		if (time_now <= next_tick) {
			continue;}
		// time, Hz low, Hz high, Hz step, samples, dbm, dbm, ...
		cal_time = localtime(&time_now);
		strftime(t_str, 50, "%Y-%m-%d, %H:%M:%S", cal_time);
		for (i=0; i<tune_count; i++) {
			fprintf(file, "%s, ", t_str);
			csv_dbm(&tunes[i], crop);
		}
		fflush(file);
		while (time(NULL) >= next_tick) {
			next_tick += interval;}
		if (single) {
			do_exit = 1;}
		if (exit_time && time(NULL) >= exit_time) {
			do_exit = 1;}
	}

	/* clean up */

	if (do_exit) {
		fprintf(stderr, "\nUser cancel, exiting...\n");}
	else {
		fprintf(stderr, "\nLibrary error %d, exiting...\n", r);}

	if (file != stdout) {
		fclose(file);}

	rtlsdr_close(dev);
	free(fft_buf);
	free(window_coefs);
	//for (i=0; i<tune_count; i++) {
	//	free(tunes[i].avg);
	//	free(tunes[i].buf8);
	//}
	return r >= 0 ? r : -r;
}

// vim: tabstop=8:softtabstop=8:shiftwidth=8:noexpandtab
