#include <stdio.h>
#include <stdbool.h>
#include <stdint.h>


/* Representation of a number of form -1^(sign) * d * 2^p2 * 5 ^p5
   where:
       d is arbitrary integer, represented as set of digits
          with (RADIX = 10**k for some k)
       p2 and p5 encode positive or negative powers of 2.

   Values are assumed to be immutable.
   All externally visible values stored in canonical form:
       If invalid, then d=0, p2=0, p5=0
       If zero then not negative and d=0, p2=0, p5=0
       If nonzero then not divisible by power of 2 or 5
*/
typedef struct {
    bool valid : 1;    // Is this a valid number
    bool negative: 1;  // Is it negative
    unsigned dcount : 30; // How many digits does it have (must be at least 1)
    int32_t pwr2;         // Power of 2
    int32_t pwr5;         // Power of 5
    uint32_t digit[1];    // Sequence of digits, each between 0 and RADIX-1
} q25_t, *q25_ptr;

void q25_free(q25_ptr q);

/* Make a fresh copy of number */
q25_ptr q25_copy(q25_ptr q);

/* Convert numbers to q25 form */
q25_ptr q25_from_64(int64_t x);
q25_ptr q25_from_32(int32_t x);
q25_ptr q25_invalid();

/* Scale by powers of 2 & 5 */
q25_ptr q25_scale(q25_ptr q, int32_t p2, int32_t p5);

/* Negative value */
q25_ptr q25_negate(q25_ptr q);

/* 
   Compute reciprocal 
   Can only compute reciprocal when d == 1
   Otherwise invalid
*/
q25_ptr q25_recip(q25_ptr q);

/* Is it valid */
bool q25_is_valid(q25_ptr q);

/* Is it zero */
bool q25_is_zero(q25_ptr q);

/* Is it one */
bool q25_is_one(q25_ptr q);

/* 
   Compare two numbers.  Return -1 (q1<q2), 0 (q1=q2), or +1 (q1>q2)
   Return -2 if either invalid
*/
int q25_compare(q25_ptr q1, q25_ptr q2);

/* Addition */
q25_ptr q25_add(q25_ptr q1, q25_ptr q2);

/* Compute 1-x */
q25_ptr q25_one_minus(q25_ptr q);

/* Multiplication */
q25_ptr q25_mul(q25_ptr q1, q25_ptr q2);

/* Read from file */
q25_ptr q25_read(FILE *infile);

/* Write to file */
void q25_write(q25_ptr q, FILE *outfile);

/* Show value in terms of its representation */
void q25_show(q25_ptr q, FILE *outfile);

/* Try converting to int64_t.  Indicate success / failure */
/* Fails if number out of range, or nonintegral */
bool get_int64(q25_ptr q, int64_t *ip);
