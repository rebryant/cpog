#include <stdbool.h>
#include "counters.h"
#include "report.h"


static int counters[COUNT_NUM];
static double timers[TIME_NUM];
static ilist histograms[HISTO_NUM];

static bool initialized = false;

static void test_init() {
    if (initialized)
	return;
    for (int c = 0; c < COUNT_NUM; c++)
	counters[c] = 0;
    for (int t = 0; t < TIME_NUM; t++)
	timers[t] = 0.0;
    for (int h = 0; h < HISTO_NUM; h++)
	histograms[h] = ilist_new(0);
    initialized = true;
}

static bool counter_ok(counter_t counter) {
    test_init();
    bool ok = counter >= 0 && counter < COUNT_NUM;
    if (!ok)
	err(false, "Invalid counter number %d\n", (int) counter);
    return ok;
}

void incr_count_by(counter_t counter, int val) {
    if (!counter_ok(counter))
	return;
    counters[counter] += val;
}

void incr_count(counter_t counter) {
    incr_count_by(counter, 1);
}

int get_count(counter_t counter) {
    if (!counter_ok(counter))
	return -1;
    return counters[counter];

}

static bool timer_ok(timer_t timer) {
    test_init();
    bool ok = timer >= 0 && timer < TIME_NUM;
    if (!ok)
	err(false, "Invalid timer number %d\n", (int) timer);
    return ok;
}

void incr_timer(timer_t timer, double secs) {
    if (!timer_ok(timer))
	return;
    timers[timer] += secs;
}

double get_timer(timer_t timer) {
    if (!timer_ok(timer))
	return -1;
    return timers[timer];

}

static bool histo_ok(histogram_t histo) {
    test_init();
    bool ok = histo >= 0 && histo < HISTO_NUM;
    if (!ok)
	err(false, "Invalid histo number %d\n", (int) histo);
    return ok;
}

void incr_histo(histogram_t histo, int datum) {
    if (!histo_ok(histo))
	return;
    int old_size = ilist_length(histograms[histo]);
    if (datum >= old_size) {
	histograms[histo] = ilist_resize(histograms[histo], datum+1);
	for (int d = old_size; d <= datum; d++)
	    histograms[histo][d] = 0;
    }
    histograms[histo][datum] ++;
}


ilist get_histo(histogram_t histo) {
    if (!histo_ok(histo))
	return NULL;
    return histograms[histo];
}
