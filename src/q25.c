#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include "q25.h"

/*
   Declarations.  The program assumes that computation is performed in decimal.
   with some number of decimal digits stored in each word
 */

/* 
   Number of decimal digits in word.
   Must fit into uint32_t
*/

#define DEBUG 0

#define Q25_DIGITS 9
#define Q25_RADIX (1000*1000*1000)

// Stress test
//#define Q25_DIGITS 3
//#define Q25_RADIX (1000)


/*
  Maintain working area for building digit representations.
  Have fixed number of words.  Use q25_t for meta information
  but separate extensible arrays for digits.
*/

/* Working area parameters */

/* How many numbers are in working area */
#define DCOUNT 3
/* How many digits are allocated in initial arrays */
#define INIT_DIGITS 100
/* Default ID for working area */
#define WID 0

bool initialized = false;
/* Per-number components */
static q25_t working_val[DCOUNT];
static uint32_t *digit_buffer[DCOUNT];
static unsigned digit_allocated[DCOUNT];

/* Lookup table for powers */
static uint32_t power2[Q25_DIGITS+1];
static uint32_t power5[Q25_DIGITS+1];
static uint32_t power10[Q25_DIGITS+1];

/* 
   Static function prototypes.
   Use id to index the different numbers
*/

/* Put into canonical form */
static void q25_canonize(int id);
// Set working value to number x < RADIX
static void q25_set(int id, uint32_t x);
// Make sure enough digits in working space
static void q25_check(int id, unsigned dcount);
static void q25_show_internal(int id, FILE *outfile);

/* Static functions */

/* Initialize data structures */
static void q25_init() {
    if (initialized)
	return;
    initialized = true;
    int id;
    for (id = 0; id < DCOUNT; id++) {
	digit_allocated[id] = INIT_DIGITS;
	digit_buffer[id] = calloc(INIT_DIGITS, sizeof(uint32_t));
	digit_buffer[id][0] = 0;
	working_val[id].valid = true;
	working_val[id].pwr2 = 0;
	working_val[id].pwr5 = 0;
	working_val[id].dcount = 1;
    }
    int i;
    uint64_t p2 = 1;
    uint64_t p5 = 1;
    for (i = 0; i <= Q25_DIGITS; i++) {
	power10[i] = p2 * p5;
	power2[i] = p2;
	p2 *= 2;
	power5[i] = p5;
	p5 *= 5;
    }
}

// Setting working value to number x < RADIX
static void q25_set(int id, uint32_t x) {
    q25_init();
    working_val[id].valid = true;
    working_val[id].pwr2 = 0;
    working_val[id].pwr5 = 0;
    working_val[id].dcount = 1;
    digit_buffer[id][0] = x;
    q25_canonize(id);
}

// Move value into working space
static void q25_work(int id, q25_ptr q) {
    q25_check(id, q->dcount);
    working_val[id].valid = q->valid;
    working_val[id].negative = q->negative;
    working_val[id].dcount = q->dcount;
    working_val[id].pwr2 = q->pwr2;
    working_val[id].pwr5 = q->pwr5;
    memcpy(digit_buffer[id], q->digit, working_val[id].dcount * sizeof(uint32_t));
}

// Make sure enough digits in working space
static void q25_check(int id, unsigned dcount) {
    q25_init();
    if (dcount <= digit_allocated[id])
	return;
    digit_allocated[id] *= 2;
    if (dcount > digit_allocated[id])
	digit_allocated[id] = dcount;
    digit_buffer[id] = realloc(digit_buffer[id], digit_allocated[id] * sizeof(uint32_t));
}

// Clear specified number of digits in workspace.  And set as length
static void q25_clear_digits(int id, unsigned len) {
    q25_check(id, len);
    memset(digit_buffer[WID], 0, len * sizeof(uint32_t));
    working_val[id].dcount = len;
}


// Divide by a number < RADIX
// Assume dividend is valid and nonzero, and divisor is nonzero
// Return remainder
static uint32_t q25_div_word(int id, uint32_t divisor) {
    if (divisor == 1)
	return 0;
    uint64_t upper = 0;
    int d;
    for (d = working_val[id].dcount-1; d >= 0; d--) {
	uint64_t dividend = (upper * Q25_RADIX) + digit_buffer[id][d];
	digit_buffer[id][d] = dividend/divisor;
	upper = dividend % divisor;
    }
    // See if upper digit set to 0
    if (working_val[id].dcount > 1 && digit_buffer[id][working_val[id].dcount-1] == 0)
	working_val[id].dcount--;
    return upper;
}

/* Take out multiples of n, where n = 2^p2 * 5^p5, and n <= RADIX */
static void q25_reduce_multiple(int id, uint32_t p2, uint32_t p5, uint32_t n) {
    uint32_t word;
    while ((word = digit_buffer[id][0])  % n == 0) {
	int pwr = 0;
	uint64_t scale = 1;
	while (scale <= Q25_RADIX && word % (scale * n) == 0) {
	    pwr ++;
	    scale *= n;
	}
	q25_div_word(id, scale);
	working_val[id].pwr2 += p2*pwr;
	working_val[id].pwr5 += p5*pwr;
    }
}

/* Take out as many multiples of 10 as possible.  Assume nonzero */
static void q25_reduce10(int id) {
    // Get as many words as possible
    uint32_t wcount = 0;
    while (wcount < working_val[id].dcount && digit_buffer[id][wcount] == 0)
	wcount++;
    // Shift words down
    uint32_t idest = 0;
    uint32_t isrc = wcount;
    while (isrc < working_val[id].dcount) {
	digit_buffer[id][idest++] = digit_buffer[id][isrc++];
    }
    working_val[id].dcount -= wcount;
    working_val[id].pwr2 += Q25_DIGITS * wcount;
    working_val[id].pwr5 += Q25_DIGITS * wcount;
    // Do the final digits
    q25_reduce_multiple(id, 1, 1, 10);
}

// Take out powers of two
static void q25_reduce2(int id) {
    q25_reduce_multiple(id, 1, 0, 2);
}

// Take out powers of five
static void q25_reduce5(int id) {
    q25_reduce_multiple(id, 0, 1, 5);
}

/* Canonize working value */
static void q25_canonize(int id) {
    if (!working_val[id].valid) {
	working_val[id].negative = false;
	working_val[id].dcount = 1;
	digit_buffer[id][0] = 0;
	working_val[id].pwr2 = 0;
	working_val[id].pwr5 = 0;
    } else {
	// Make sure have the right number of digits
	while (working_val[id].dcount > 1 && digit_buffer[id][working_val[id].dcount-1] == 0)
	    working_val[id].dcount--;
	if (working_val[id].dcount == 1 && digit_buffer[id][0] == 0) {
	    working_val[id].negative = false;
	    working_val[id].pwr2 = 0;
	    working_val[id].pwr5 = 0;
	} else {
	    // Diminish by powers of 10, 2, and 5
	    q25_reduce10(id);
	    q25_reduce2(id);
	    q25_reduce5(id);
	}
    }
}

// Convert the working version into a true q25_t
static q25_ptr q25_build(int id) {
    q25_canonize(id);
    size_t len = sizeof(q25_t) + (working_val[id].dcount - 1) * sizeof(uint32_t);
    q25_ptr result = malloc(len);
    if (result == NULL)
	return NULL;
    result->valid = working_val[id].valid;
    result->negative = working_val[id].negative;
    result->dcount = working_val[id].dcount;
    result->pwr2 = working_val[id].pwr2;
    result->pwr5 = working_val[id].pwr5;
    memcpy(result->digit, digit_buffer[id], working_val[id].dcount * sizeof(uint32_t));
    return result;
}

// Multiply by a number < RADIX
// Assume multiplier is nonzero
static void q25_mul_word(int id, uint32_t multiplier) {
#if DEBUG
    printf("  Multiplying by %u\n", multiplier);
#endif
    q25_check(id, working_val[id].dcount+1);
    if (multiplier == 1)
	return;
    uint64_t upper = 0;
    int d;
    for (d = 0 ; d < working_val[id].dcount; d++) {
	uint64_t ndigit = upper + (uint64_t) multiplier * digit_buffer[id][d];
	digit_buffer[id][d] = ndigit % Q25_RADIX;
	upper = ndigit / Q25_RADIX;
    }
    // See if upper digit set to 0
    if (upper > 0) {
	digit_buffer[id][d] = upper;
	working_val[id].dcount++;
    }
}

// Scale number by power of 2, 5, or 10
static void q25_scale_digits(int id, bool p2, int pwr) {
    int p;
    if (p2)
	working_val[id].pwr2 -= pwr;
    else
	working_val[id].pwr5 -= pwr;
    uint32_t multiplier = p2 ? power2[Q25_DIGITS] : power5[Q25_DIGITS];
    while (pwr > Q25_DIGITS) {
	q25_mul_word(id, multiplier);
	pwr -= Q25_DIGITS;
    }
    multiplier = p2 ? power2[pwr] : power5[pwr];
    q25_mul_word(id, multiplier);
}

/* 
   Compare two working numbers.
   Must have already been scaled so that both numbers have same values for pwr2 & pwr5
   Return -1 (q1<q2), 0 (q1=q2), or +1 (q1>q2)
   Return -2 if either invalid
*/
static int q25_compare_working_magnitude(int id1, int id2) {
    if (working_val[id1].dcount < working_val[id2].dcount)
	return -1;
    if (working_val[id1].dcount > working_val[id2].dcount)
	return 1;
    int d;
    for (d = working_val[id1].dcount-1; d >= 0; d--) {
	if (digit_buffer[id1][d] < digit_buffer[id2][d])
	    return -1;
	if (digit_buffer[id1][d] > digit_buffer[id2][d])
	    return 1;
    }
    return 0;
}

/* How many decimal digits are in representation? */
static int q25_length10(int id) {
    if (!working_val[id].valid)
	return -1;
    int n10 = (working_val[id].dcount-1) * Q25_DIGITS;
    uint32_t word = digit_buffer[id][working_val[id].dcount-1];
    while (word > 0) {
	n10++;
	word = word/10;
    }
    return n10;
}

/* Get individual decimal digit */
static unsigned q25_get_digit10(int id, int index) {
    int digit = index / Q25_DIGITS;
    int offset = index % Q25_DIGITS;
    uint32_t power = power10[offset];
    if (digit < 0 || digit >= working_val[id].dcount)
	return 0;
    uint32_t word = digit_buffer[id][digit];
    return (word / power) % 10;
}

/* Show internal representation */
static void q25_show_internal(int id, FILE *outfile) {
    if (!working_val[id].valid)
	fprintf(outfile, "INVALID");
    fprintf(outfile, "[%c,p2=%d,p5=%d", working_val[id].negative ? '-' : '+', working_val[id].pwr2, working_val[id].pwr5);
    int d;
    for (d = working_val[id].dcount-1; d >= 0; d--) {
	fprintf(outfile, "|");
	fprintf(outfile, "%u", digit_buffer[id][d]);
    }
    fprintf(outfile, "]");
}


/**** Externally visible functions ****/

void q25_free(q25_ptr q) {
    free((void *) q);
}

/* Convert int64_t to q25 form */
#define I64_DIGITS 20
q25_ptr q25_from_64(int64_t x) {
    int wcount = (I64_DIGITS + Q25_DIGITS-1)/Q25_DIGITS;
    q25_check(WID, wcount);
    q25_set(WID, 0);
    if (x == 0)
	return q25_build(WID);
    if (x < 0) {
	working_val[WID].negative = true;
	x = -x;
    }
    working_val[WID].dcount = 0;
    while (x > 0) {
	digit_buffer[WID][working_val[WID].dcount++] = x % Q25_RADIX;
	x = x / Q25_RADIX;
    }
    return q25_build(WID);
}

/* Convert int32_t to q25 form */
#define I32_DIGITS 10
q25_ptr q25_from_32(int32_t x) {
    int wcount = (I32_DIGITS + Q25_DIGITS-1)/Q25_DIGITS;
    q25_check(WID, wcount);
    q25_set(WID, 0);
    if (x == 0)
	return q25_build(WID);
    if (x < 0) {
	working_val[WID].negative = true;
	x = -x;
    }
    working_val[WID].dcount = 0;
    while (x > 0) {
	digit_buffer[WID][working_val[WID].dcount++] = x % Q25_RADIX;
	x = x / Q25_RADIX;
    }
    return q25_build(WID);
}

q25_ptr q25_invalid() {
    q25_set(WID, 0);
    working_val[WID].valid = false;
    return q25_build(WID);
}

q25_ptr q25_copy(q25_ptr q) {
    q25_work(WID, q);
    return q25_build(WID);
}

q25_ptr q25_scale(q25_ptr q, int32_t p2, int32_t p5) {
    q25_work(WID, q);
    working_val[WID].pwr2 += p2;
    working_val[WID].pwr5 += p5;
    return q25_build(WID);
}

q25_ptr q25_negate(q25_ptr q) {
    q25_work(WID, q);
    working_val[WID].negative = !working_val[WID].negative;
    return q25_build(WID);
}

// Can only compute reciprocal when d == 1
// Otherwise invalid
q25_ptr q25_recip(q25_ptr q) {
    q25_set(WID, 1);
    if (!q->valid || q->dcount > 1 || q->digit[0] != 1) {
	working_val[WID].valid = false;
    } else {
	working_val[WID].pwr2 = -q->pwr2;
	working_val[WID].pwr5 = -q->pwr5;
    }
    return q25_build(WID);
}

bool q25_is_valid(q25_ptr q) {
    return q->valid;
}

bool q25_is_zero(q25_ptr q) {
    return q->valid && q->dcount == 1 && q->digit[0] == 0;
}

bool q25_is_one(q25_ptr q) {
    return q->valid && q->dcount == 1 && q->digit[0] == 1 
	&& q->pwr2 == 0 && q->pwr5 == 0;
}


/* 
   Compare two numbers.  Return -1 (q1<q2), 0 (q1=q2), or +1 (q1>q2)
   Return -2 if either invalid
*/
int q25_compare(q25_ptr q1, q25_ptr q2) {
    if (q1->valid != q2->valid)
	return -2;
    if (q1->negative && !q2->negative)
	return -1;
    if (!q1->negative && q2->negative)
	return 1;
    if (q1->negative) {
	// Swap two, so that can compare digits
	q25_ptr qt = q1; q1 = q2; q2 = qt;
    }
    /* Must move arguments into working area so that can scale */
    q25_work(1, q1);
    q25_work(2, q2);
    int diff2 = working_val[1].pwr2 - working_val[2].pwr2;
    if (diff2 > 0) {
	q25_scale_digits(1, true, diff2);
    } else if (diff2 < 0) {
	q25_scale_digits(2, true, -diff2);
    }
    int diff5 = working_val[1].pwr5 - working_val[2].pwr5;
    if (diff5 > 0) {
	q25_scale_digits(1, false, diff5);
    } else if (diff5 < 0) {
	q25_scale_digits(2, false, -diff5);
    }
    return q25_compare_working_magnitude(1, 2);
}


q25_ptr q25_add(q25_ptr q1, q25_ptr q2) {
    /* Must move arguments into working area.  Build result with id 0 */
    q25_work(1, q1);
    q25_work(2, q2);
#if DEBUG
    printf("  Working argument 1:");
    q25_show_internal(1, stdout);
    printf("\n  Working argument 2:");
    q25_show_internal(2, stdout);
    printf("\n");
#endif
    int diff2 = working_val[1].pwr2 - working_val[2].pwr2;
    if (diff2 > 0) {
	q25_scale_digits(1, true, diff2);
    } else if (diff2 < 0) {
	q25_scale_digits(2, true, -diff2);
    }
    int diff5 = working_val[1].pwr5 - working_val[2].pwr5;
    if (diff5 > 0) {
	q25_scale_digits(1, false, diff5);
    } else if (diff5 < 0) {
	q25_scale_digits(2, false, -diff5);
    }
#if DEBUG
    printf("  Scaled working argument 1:");
    q25_show_internal(1, stdout);
    printf("\n  Scaled working argument 2:");
    q25_show_internal(2, stdout);
    printf("\n");
#endif
    if (working_val[1].negative == working_val[2].negative) {
	unsigned ndcount = working_val[1].dcount;
	if (working_val[2].dcount > ndcount)
	    ndcount = working_val[2].dcount;
	ndcount += 1;
	q25_set(WID, 0);
	q25_check(WID, ndcount);
	working_val[WID].negative = working_val[1].negative;
	working_val[WID].pwr2 = working_val[1].pwr2;
	working_val[WID].pwr5 = working_val[1].pwr5;
	working_val[WID].dcount = ndcount;
	q25_clear_digits(WID, ndcount);
	uint32_t carry = 0;
	int d;
	for (d = 0; d < ndcount; d++) {
	    uint64_t digit = carry;
	    if (d < working_val[1].dcount)
		digit += digit_buffer[1][d];
	    if (d < working_val[2].dcount)
		digit += digit_buffer[2][d];
	    digit_buffer[WID][d] = digit % Q25_RADIX;
	    carry = digit / Q25_RADIX;
	}
    } else {
	int diff = q25_compare_working_magnitude(1, 2);
	q25_set(WID, 0);
	if (diff != 0) {
	    int tid = diff < 0 ? 2 : 1;
	    int bid = diff < 0 ? 1 : 2;
	    working_val[WID].negative = working_val[tid].negative;
	    working_val[WID].pwr2 = working_val[1].pwr2;
	    working_val[WID].pwr5 = working_val[1].pwr5;
	    working_val[WID].dcount = working_val[tid].dcount;
	    q25_check(WID, working_val[tid].dcount);
	    q25_clear_digits(WID, working_val[tid].dcount);
	    int32_t borrow = 0;
	    int d;
	    for (d = 0; d < working_val[tid].dcount; d++) {
		int64_t digit = -borrow;
		digit += digit_buffer[tid][d];
		if (d < working_val[bid].dcount)
		    digit -= digit_buffer[bid][d];
		if (digit < 0) {
		    digit += Q25_RADIX;
		    borrow = 1;
		} else 
		    borrow = 0;
		digit_buffer[WID][d] = digit;
	    }
	}
    }
#if DEBUG
    printf("  Working Sum:");
    q25_show_internal(WID, stdout);
    printf("\n");
#endif
    return q25_build(WID);
}

q25_ptr q25_one_minus(q25_ptr q) {
    q25_ptr one = q25_from_32(1);
    if (q25_is_zero(q))
	return one;
    /* Hack.  Temporarily negate argument */
    q->negative = !q->negative;
    q25_ptr sum = q25_add(one, q);
    q->negative = !q->negative;
    q25_free(one);
    return sum;
}

q25_ptr q25_mul(q25_ptr q1, q25_ptr q2) {
    if (q25_is_zero(q1) || !q1->valid)
	return q25_copy(q1);
    if (q25_is_zero(q2) || !q2->valid)
	return q25_copy(q2);
    q25_set(WID, 0);
    // Figure out sign
    working_val[WID].negative = (q1->negative != q2->negative);
    // Set powers
    working_val[WID].pwr2 = q1->pwr2 + q2->pwr2;
    working_val[WID].pwr5 = q1->pwr5 + q2->pwr5;
    // Clear out space for the product
    unsigned len = q1->dcount + q2->dcount + 1;
    q25_clear_digits(WID, len);
    // Make sure q1 is longer
    if (q1->dcount < q2->dcount) {
	q25_ptr qt = q1; q1 = q2; q2 = qt;
    }
    unsigned d1, d2;
    for (d2 = 0; d2 < q2->dcount; d2++) {
	uint64_t digit2 = q2->digit[d2];
	uint64_t carry = 0;
	for (d1 = 0; d1 < q1->dcount; d1++) {
	    uint64_t ndigit = q1->digit[d1] * digit2 + carry + digit_buffer[WID][d1+d2];
	    digit_buffer[WID][d1+d2] = ndigit % Q25_RADIX;
	    carry = ndigit / Q25_RADIX;
	}
	digit_buffer[WID][d1+d2] = carry;
    }
    return q25_build(WID);
}

q25_ptr q25_read(FILE *infile) {
    /* Fill up digit buffer in reverse order */
    int d = 0;
    q25_check(1, d+1);
    digit_buffer[1][d] = 0;
    bool negative = false;
    int pwr10 = 0;
    bool got_point = false;
    /* Number of base 10 digits read */
    int n10 = 0;
    bool first = true;
    while (true) {
	int c = fgetc(infile);
	if (c == '-') {
	    if (first) {
		negative = true;
		first = false;
		continue;
	    }
	    else {
		ungetc(c, infile);
		break;
	    }
	} else if (c == '.') {
	    if (got_point) {
		ungetc(c, infile);
		break;
	    } else
		got_point = true;
	} else if (isdigit(c)) {
	    n10++;
	    if (got_point)
		pwr10--;
	    if (n10 > Q25_DIGITS && (n10-1) % Q25_DIGITS == 0) {
		// Time to start new word
		d++;
		q25_check(1, d+1);
		digit_buffer[1][d] = 0;
	    }
	    unsigned dig = c - '0';
	    digit_buffer[1][d] = 10 * digit_buffer[1][d] + dig;
	} else {
	    ungetc(c, infile);
	    break;
	}
	first = false;
    }
    bool valid = n10 > 0;
    if (valid) {
	// See if there's an exponent
	int c = fgetc(infile);
	if (c == 'e') {
	    // Deal with exponent
	    bool exp_negative = false;
	    int nexp = 0;
	    int exponent = 0;
	    bool exp_first = true;
	    while (true) {
		c = fgetc(infile);
		if (c == '-') {
		    if (exp_first)
			exp_negative = true;
		    else {
			ungetc(c, infile);
			valid = false;
			break;
		    }
		} else if (isdigit(c)) {
		    nexp++;
		    unsigned dig = c - '0';
		    exponent = 10 * exponent + dig;
		} else {
		    ungetc(c, infile);
		    break;
		}
		exp_first = false;
	    }
	    valid = valid && nexp > 0;
	    if (exp_negative)
		exponent = -exponent;
	    pwr10 += exponent;
	} else
	    ungetc(c, infile);
    }
    if (!valid) {
	q25_set(WID, 0);
	working_val[WID].valid = false;
	return q25_build(WID);
    }
    q25_set(WID, 0);
    working_val[WID].negative = negative;
    // Reverse the digits
    unsigned dcount = (n10 + Q25_DIGITS-1) / Q25_DIGITS;
    q25_check(WID, dcount);
    for (d = 0; d < dcount; d++) {
	digit_buffer[WID][d] = digit_buffer[1][dcount - 1 - d];
    }
    // Now could have a problem with the bottom word
    // Slide up to top and let the canonizer fix things
    unsigned extra_count = n10 % Q25_DIGITS;
    if (extra_count > 0) {
	unsigned scale = Q25_DIGITS-extra_count;
	unsigned multiplier = power10[scale];
	digit_buffer[WID][0] *= multiplier;
	pwr10 -= scale;
    }
    working_val[WID].dcount = dcount;
    working_val[WID].pwr2 = pwr10;
    working_val[WID].pwr5 = pwr10;
#if DEBUG
    printf("  Read value before canonizing: ");
    q25_show_internal(WID, stdout);
    printf("\n");
#endif
    return q25_build(WID);
}

void q25_write(q25_ptr q, FILE *outfile) {
    if (!q->valid) {
	fprintf(outfile, "INVALID");
	return;
    }
    if (q->dcount == 1 && q->digit[0] == 0) {
	fprintf(outfile, "0");
	return;
    }    

    if (q->negative)
	fputc('-', outfile);
    q25_work(WID, q);

    // Scale so that pwr2 = pwr5
    int diff = working_val[WID].pwr2 - working_val[WID].pwr5;
    if (diff > 0) {
	q25_scale_digits(WID, true, diff);
    } else if (diff < 0) {
	q25_scale_digits(WID, false, -diff);
    }
#if DEBUG
    printf("  Scaled for printing: ");
    q25_show_internal(WID, stdout);
    printf("\n");
#endif
    int n10 = q25_length10(WID);
    int p10 = working_val[WID].pwr2;
    int i;
    if (p10 >= 0) {
	for (i = n10-1; i >= 0; i--) {
	    int d10 = q25_get_digit10(WID, i);
	    char d = '0' + d10;
	    fputc(d, outfile);
	}
	while (p10-- > 0)
	    fputc('0', outfile);
    } else if (-p10 >= n10) {
	fputc('0', outfile);
	fputc('.', outfile);
	while (-p10 > n10) {
	    fputc('0', outfile);
	    p10++;
	}
	for (i = n10-1; i >= 0; i--) {
	    int d10 = q25_get_digit10(WID, i);
	    char d = '0' + d10;
	    fputc(d, outfile);
	}
    } else {
	for (i = n10-1; i >= 0; i--) {
	    int d10 = q25_get_digit10(WID, i);
	    char d = '0' + d10;
	    fputc(d, outfile);
	    if (i == -p10)
		fputc('.', outfile);
	}
    }
}

/* Show value in terms of its representation */
void q25_show(q25_ptr q, FILE *outfile) {
    q25_work(WID, q);
    q25_show_internal(WID, outfile);
}

/* Try converting to int64_t.  Indicate success / failure */
bool get_int64(q25_ptr q, int64_t *ip) {
    if (!q->valid || q->pwr2 < 0 || q->pwr5 < 0)
	return false;
    if (q->negative) {
	q25_ptr qmin = q25_from_64(INT64_MIN);
	if (q25_compare(q, qmin) < 0)
	    return false;
    } else {
	q25_ptr qmax = q25_from_64(INT64_MAX);
	if (q25_compare(q, qmax) > 0)
	    return false;
    }
    int64_t val = 0;
    int d;
    if (q->negative) {
	for (d = q->dcount-1; d >= 0; d--) {
	    val = val * Q25_RADIX + -q->digit[d];
	}
    } else {
	for (d = q->dcount-1; d >= 0; d--) {
	    val = val * Q25_RADIX + q->digit[d];
	}
    }
    int i;
    for (i = 0; i < q->pwr2; i++)
	val *= 2;
    for (i = 0; i < q->pwr5; i++)
	val *= 5;
    *ip = val;
    return true;
}

