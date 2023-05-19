/*========================================================================
  Copyright (c) 2022 Randal E. Bryant, Carnegie Mellon University

  Permission is hereby granted, free of
  charge, to any person obtaining a copy of this software and
  associated documentation files (the "Software"), to deal in the
  Software without restriction, including without limitation the
  rights to use, copy, modify, merge, publish, distribute, sublicense,
  and/or sell copies of the Software, and to permit persons to whom
  the Software is furnished to do so, subject to the following
  conditions:
  
  The above copyright notice and this permission notice shall be
  included in all copies or substantial portions of the Software.
  
  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
  EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
  MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
  NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
  BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
  ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
  CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
  SOFTWARE.
========================================================================*/

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <ctype.h>
#include <stdbool.h>
#include <sys/time.h>
#include <limits.h>
#include <stdarg.h>
#include "q25.h"

void usage(char *name) {
    printf("Usage: %s [-h] [-v VERB] [-1] FILE.cnf [FILE.cpog]\n", name);
    printf(" -h           Print this message\n");
    printf(" -v VERB      Set verbosity level\n");
    printf(" -1           Perform one-sided check (don't verify assertions)\n");
    printf("    FILE.cnf  Input CNF file\n");
    printf("    FILE.cpog Input CPOG file\n");
    exit(0);
}

/*============================================
  Macro parameters
============================================*/

#define ERROUT stdout
#define MIN_SIZE 10
#define MAX_GAP 10
#define GROW_RATIO 1.45
#define DPREFIX "CHECK"
#define __cfunc__ (char *) __func__

/* How many ints fit into a single chunk (2^20 = 4MB) */
#define CHUNK_SIZE (1L << 20)
/* What is assumed limit of VM (128 GB) */
#define VM_LIMIT (1L << 37)
/* What is the maximum number of chunks (32K) */
#define CHUNK_MAX (VM_LIMIT/(CHUNK_SIZE * sizeof(int)))

/*============================================
  Global variables.  Others are later in file.
============================================*/

/* Options */
int verb_level = 3;

int one_sided = false;

/* Allow RUP proofs that encounter conflict before final hint */
bool early_rup = true;

/* Information for error reporting */
char *current_file = "";
int line_count = 0;

int input_clause_count = 0;
int input_variable_count = 0;
int variable_limit = 0;

/* Allow declaration of root node.  Make sure it matches literal in
   only remaining unit clause */
int declared_root = 0;

/*============================================
  Prototypes
============================================*/

void clause_show(FILE *out, int cid, bool endline);

/*============================================
  Utility functions
============================================*/

double tod() {
    struct timeval tv;
    if (gettimeofday(&tv, NULL) == 0)
	return (double) tv.tv_sec + 1e-6 * tv.tv_usec;
    else
	return 0.0;
}

void err_printf(char *fun, char *fmt, ...) {
    va_list ap;
    fprintf(ERROUT, "ERROR. File %s. Line %d. Function %s. ", current_file, line_count+1, fun);
    va_start(ap, fmt);
    vfprintf(ERROUT, fmt, ap);
    va_end(ap);
    exit(1);
}

void info_printf(int vlevel, char *fmt, ...) {
    if (vlevel > verb_level)
	return;
    va_list ap;
    fprintf(stdout, "File %s. Line %d:", current_file, line_count+1);
    va_start(ap, fmt);
    vfprintf(stdout, fmt, ap);
    va_end(ap);
}

void data_printf(int vlevel, char *fmt, ...) {
    if (vlevel > verb_level)
	return;
    va_list ap;
    fprintf(stdout, "%s: ", DPREFIX);
    va_start(ap, fmt);
    vfprintf(stdout, fmt, ap);
    va_end(ap);
}

/*============================================
   Integer lists
============================================*/

/*
  Data type ilist is used to represent clauses and clause id lists.
  These are simply lists of integers, where the value at position -1
  indicates the list length and the value at position -2 indicates the
  maximum list length.  The value at position -2 is positive for
  statically-allocated ilists and negative for ones that can be
  dynamically resized.
*/
typedef int *ilist;
  
/* Macros */
/*
  Difference between ilist maximum length and number of allocated
  integers
 */
#define ILIST_OVHD 2

#define ILIST_BASE(ils) ((ils)-ILIST_OVHD)
#define ILIST_LENGTH(ils) ((ils)[-1])
#define IABS(x) ((x)<0?(-x):(x))
#define ILIST_MAXLENGTHFIELD(ils) ((ils)[-2])
#define ILIST_MAXLENGTH(ils) (IABS(ILIST_MAXLENGTHFIELD(ils)))

/* Allocate a new ilist. */
ilist ilist_new(int max_length) {
    if (max_length == 0)
	max_length++;
    int *p = calloc(max_length + ILIST_OVHD, sizeof(int));
    if (p == NULL)
	err_printf("ilist_new", "Failed to allocate ilist of length %d\n", max_length);
    ilist result = p+ILIST_OVHD;
    ILIST_LENGTH(result) = 0;
    ILIST_MAXLENGTHFIELD(result) = -max_length;
    return result;
}

/* Free allocated ilist.  Will only free ones allocated via ilist_new */
void ilist_free(ilist ils) {
    if (!ils)
	return;
    if (ILIST_MAXLENGTHFIELD(ils) < 0) {
	int *p = ILIST_BASE(ils);
	free(p);
    }
}

/* Return number of elements in ilist */
int ilist_length(ilist ils) {
    return ILIST_LENGTH(ils);
}

/*
  Change size of ilist.  Can be shorter or longer than current.
  When lengthening, new contents are undefined
*/
ilist ilist_resize(ilist ils, int nlength) {
    int list_max_length = ILIST_MAXLENGTHFIELD(ils);
    int true_max_length = IABS(list_max_length);
    if (nlength > true_max_length) {
	if (list_max_length < 0) {
	    int *p = ILIST_BASE(ils);
	    int old_tml = true_max_length;
	    /* Dynamically resize */
	    true_max_length = (int) (true_max_length * GROW_RATIO);
	    if (nlength > true_max_length)
		true_max_length = nlength;
	    p = realloc(p, (true_max_length + ILIST_OVHD) * sizeof(int));
	    if (p == NULL)
		err_printf(__cfunc__, "Failed to grow ilist allocation from %d to %d\n",
			old_tml, true_max_length);
	    ils = p+ILIST_OVHD;
	    ILIST_MAXLENGTHFIELD(ils) = -true_max_length;
	} else 
	    /* Need to throw an error here */
	    err_printf(__cfunc__, "Cannot resize static ilist beyond initial allocation %d", true_max_length);
    }
    ILIST_LENGTH(ils) = nlength;
    return ils;
}

/*
  Add new value(s) to end of ilist.
  For dynamic ilists, the value of the pointer may change
*/
ilist ilist_push(ilist ils, int val) {
    int length = ILIST_LENGTH(ils);
    int nlength = length+1;
    ils = ilist_resize(ils, nlength);
    if (!ils)
	/* Want to throw an exception here */
	err_printf(__cfunc__, "Couldn't allocate space for list of length %d", nlength);
    ils[length] = val;
    ILIST_LENGTH(ils) = nlength;
    return ils;
}

/*
  Sort integers in ascending order
 */
int int_compare_ilist(const void *i1p, const void *i2p) {
    int i1 = *(int *) i1p;
    int i2 = *(int *) i2p;
    if (i1 < i2)
	return -1;
    if (i1 > i2)
	return 1;
    return 0;
}

/*
  Put elements of ilist into ascending order
 */
void ilist_sort(ilist ils) {
    qsort((void *) ils, ilist_length(ils), sizeof(int), int_compare_ilist);
}

/*
  Print elements of an ilist separated by sep
 */
int ilist_print(ilist ils, FILE *out, const char *sep) {
    int i;
    int rval = 0;
    const char *space = "";
    if (ils == NULL) {
	rval = fprintf(out, "NULL");
	return rval;
    }
    for (i = 0; i < ilist_length(ils); i++) {
	int pval = fprintf(out, "%s%d", space, ils[i]);
	if (pval < 0)
	    return pval;
	rval += pval;
	space = sep;
    }
    return rval;
}

/*
  Print elements of an ilist separated by sep.  Return number of characters written
 */
int ilist_format(ilist ils, char *out, const char *sep, int maxlen) {
    int i;
    const char *space = "";
    int len = 0;
    for (i = 0; i < ilist_length(ils); i++) {
	if (len >= maxlen)
	    break;
	int xlen = snprintf(out+len, maxlen-len, "%s%d", space, ils[i]);
	len += xlen;
	space = sep;
    }
    out[len] = '\0';
    return len;
}

/****************************
Integer Sets.  Extend ilist by listing all members in ascending order
*****************************/
/*
  Test whether value is member of list
*/
bool ilist_is_member(ilist ils, int val) {
    int i;
    for (i = 0; i < ilist_length(ils); i++) {
	int lval = ils[i];
	if (val == lval)
	    return true;
	if (val < lval)
	    return false;
    }
    return false;
}

bool ilist_is_disjoint(ilist ils1, ilist ils2) {
    int i1 = 0;
    int i2 = 0;
    int n1 = ilist_length(ils1);
    int n2 = ilist_length(ils2);
    while (i1 < n1 && i2 < n2) {
	int v1 = ils1[i1];
	int v2 = ils2[i2];
	if (v1 == v2)
	    return false;
	if (v1 < v2) 
	    i1++;
	else
	    i2++;
    }
    return true;
}

ilist ilist_union(ilist ils1, ilist ils2) {
    int i1 = 0;
    int i2 = 0;
    int n1 = ilist_length(ils1);
    int n2 = ilist_length(ils2);
    ilist rls = ilist_new(n1 < n2 ? n2 : n1);
    while (i1 < n1 && i2 < n2) {
	int v1 = ils1[i1];
	int v2 = ils2[i2];
	if (v1 < v2) {
	    rls = ilist_push(rls, v1);
	    i1++;
	} else if (v2 < v1) {
	    rls = ilist_push(rls, v2);
	    i2++;
	} else {
	    rls = ilist_push(rls, v1);
	    i1++; i2++;
	}
    }
    while (i1 < n1) {
	int v1 = ils1[i1++];
	rls = ilist_push(rls, v1);
    }
    while (i2 < n2) {
	int v2 = ils2[i2++];
	rls = ilist_push(rls, v2);
    }
    return rls;
}

/*============================================
  Set of literals for performing unit propagation
============================================*/

/*
  Represent set of literals as array indexed by variable.
  Maintain counter "lset_generation"
  Entry +lset_generation indicates positive literal
  Entry -lset_generation indicates negative literal
  Any entry with value < |lset_generation| indicates neither literal in set
 */

int lset_generation = 0;
int *lset_array = NULL;
size_t lset_asize = 0;

void lset_init(int var) {
    lset_asize = MIN_SIZE;
    if (var > lset_asize)
	lset_asize = var;
    lset_array = calloc(lset_asize, sizeof(int));
    if (lset_array == NULL)
	err_printf(__cfunc__, "Couldn't allocate initial literal array of size %zd\n", lset_asize);
    lset_generation = 1;
}

void lset_clear() {
    lset_generation++;
    if (lset_generation < 0) {
	int var;
	for (var = 1; var <= lset_asize; var++) 
	    lset_array[var-1] = 0;
	lset_generation = 1;
    }
}

void lset_check_size(int var) {
    if (var <= lset_asize)
	return;
    if (lset_asize == 0) {
	lset_init(var);
	return;
    }
    size_t nasize = (size_t) (lset_asize * GROW_RATIO);
    if (nasize < var)
	nasize = var;
    lset_array = realloc(lset_array, nasize * sizeof(int));
    info_printf(3, "Resizing lset array %zd --> %zd\n", lset_asize, nasize);
    if (lset_array == NULL)
	err_printf(__cfunc__, "Couldn't grow literal array size to %zd\n", nasize);
    int nvar;
    for (nvar = lset_asize+1; nvar <= nasize; nvar++)
	lset_array[nvar-1] = 0;
    lset_asize = nasize;
}

int lset_get_lit(int var) {
    if (var <= 0 || var > lset_asize)
	return 0;
    int g = lset_array[var-1];
    if (g == lset_generation)
	return var;
    if (g == -lset_generation)
	return -var;
    return 0;
}

/* Attempt to add literal to set.  Return false if already have opposite literal */
bool lset_add_lit(int lit) {
    int var = IABS(lit);
    lset_check_size(var);
    int olit = lset_get_lit(var);
    if (olit != 0 && olit != lit)
	return false;
    int val = lit > 0 ? lset_generation : -lset_generation;
    lset_array[var-1] = val;
    return true;
}

void lset_show(FILE *out) {
    int var;
    fprintf(out, "[");
    bool first = true;
    for (var = 1; var <= lset_asize; var++) {
	int lit = lset_get_lit(var);
	if (lit == 0)
	    continue;
	if (first)
	    fprintf(out, "%d", lit);
	else
	    fprintf(out, ", %d", lit);
	first = false;
    }
    fprintf(out, "]");
}

/*============================================
  Processing Input
============================================*/

typedef enum {TOK_INT, TOK_STRING, TOK_STAR, TOK_EOF, TOK_EOL, TOK_NONE, TOK_UNKNOWN} token_t;

char *token_name[7] = { "integer", "string", "star", "EOF", "EOL", "NONE", "UNKNOWN" };

#define TOKEN_MAX 100
char token_last[TOKEN_MAX];
int token_value = 0;
FILE *token_file = NULL;
int token_pos = 0;

void token_setup(char *fname) {
    token_file = fopen(fname, "r");
    current_file = strdup(fname);
    if (token_file == NULL)
	err_printf(__cfunc__, "Couldn't open file '%s'\n", fname);
    line_count = 0;
}

void token_finish() {
    fclose(token_file);
    token_file = NULL;
}

bool skip_space() {
    int c;
    do
	c = fgetc(token_file);
    while(c != '\n' && c != EOF && isspace(c));
    if (c == EOF || c == '\n')
	return false;
    ungetc(c, token_file);
    return true;
}

token_t token_next() {
    int sign = 1;
    int mag = 0;
    token_t ttype = TOK_NONE;
    token_pos = 0;
    token_last[token_pos] = '\0';
    token_value = 0;
    int c;
    bool done = false;
    while (!done) {
	c = fgetc(token_file);
	if (c == EOF) {
	    ttype = TOK_EOF;
	    done = true;
	} else  if (c == '\n') {
	    line_count ++;
	    ttype = TOK_EOL;
	    done = true;
	} else if (!isspace(c)) {
	    ungetc(c, token_file);
	    break;
	}
    }

    while (!done) {
	if (token_pos >= TOKEN_MAX-1) {
	    ttype = TOK_UNKNOWN;
	    done = true;
	}
	c = fgetc(token_file);
	if (c == '-') {
	    if (ttype != TOK_NONE) {
		ttype = TOK_UNKNOWN;
		done = true;
	    } else {
		sign = -sign;
		ttype = TOK_INT;
		token_last[token_pos++] = c;
		token_last[token_pos] = '\0';
	    }
	} else if (isdigit(c)) {
	    if (ttype != TOK_NONE && ttype != TOK_INT) {
		ttype =  TOK_UNKNOWN;
		done = true;
	    } else {
		ttype = TOK_INT;
		mag = 10 * mag + (c - '0');
		token_last[token_pos++] = c;
		token_last[token_pos] = '\0';
		token_value = sign * mag;
	    }
	} else if (isspace(c)) {
	    if (c == '\n') {
		ungetc(c, token_file);
	    }
	    done = true;
	} else if (c == '*') {
	    if (ttype != TOK_NONE) {
		ttype = TOK_UNKNOWN;
		done = true;
	    } else {
		token_last[token_pos++] = c;
		token_last[token_pos] = '\0';
		ttype = TOK_STAR;
	    }
	} else {
	    if (ttype != TOK_NONE && ttype != TOK_STRING) {
		ttype = TOK_UNKNOWN;
		done = true;
	    } else {
		ttype = TOK_STRING;
		token_last[token_pos++] = c;
		token_last[token_pos] = '\0';
	    }
	}
    }
    info_printf(4, "Read token.  Token = '%s'.  Type = %s\n", token_last, token_name[ttype]);
    return ttype;
}

void token_confirm_eol() {
    /* Done */
    token_t token = token_next();
    if (token != TOK_EOL)
	err_printf(__cfunc__, "Expected end of line.  Got %s ('%s') instead\n", token_name[token], token_last);
}

void token_find_eol() {
    int c;
    while (true) {
	c = fgetc(token_file);
	if (c == EOF)
	    return;
	if (c == '\n') {
	    line_count ++;
	    return;
	}
    }
}

/*============================================
  Core data structures
============================================*/

/* 
   Maintain set of all clauses as set of chunks.  Within a chunk,
   clauses are organized as zero-terminated sequences of int's.  A
   clause does not break across chunks
*/

/*
  Fixed array containing pointers to all chunks.  Individual chunks
  are allocated dynamically.
*/
int *chunk_set[CHUNK_MAX];

/* How many chunks have been allocated? */
int chunk_count = 0;

/* How much of the current chunk has been used */
int chunk_used = 0;

/* Tracking clauses */
int clause_count = 0;
int clause_last_id = 0;

// Working area for creating a new clause
ilist current_clause = NULL;

/* 
   For each extension variable, count of number of clauses containing
   reference to it.
   Indexed by xvar - (input_variable_count + 1);
*/
ilist clause_xvar_reference = NULL;

/*
  Assume that clauses come in consecutively numbered blocks, but with gaps between them
  Maintain as array of blocks
 */

typedef struct BELE {
    int start_id;  // Clause ID of initial entry
    int length;    // Number of (possibly null) clauses in block
    ilist chunk;   // Sequence of chunk IDs (numbered from 0)
    ilist offset;  // Sequence of clause offsets within chunk
} clause_block_t;

clause_block_t *clause_blocks = NULL;
int clause_block_alloc = 0;
int clause_block_count = 0;

/*
  For mutual exclusion proof of sum operation, must ensure that only
  defining clauses are referenced in hints.  Keep track of ranges of
  clause IDs that form hints as pair of ilist's
 */
ilist clause_defining_start_id = NULL;
ilist clause_defining_end_id = NULL;

/* Operations */
void clause_init() {
    /* Allocate a single starting chunk */
    chunk_set[chunk_count] = calloc(CHUNK_SIZE, sizeof(int));
    if (chunk_set[chunk_count] == NULL)
	err_printf(__cfunc__, "Couldn't allocate space for clause chunk %d\n", chunk_count);	
    chunk_count++;
    current_clause = ilist_new(0);
    clause_block_alloc = 10;
    clause_blocks = calloc(clause_block_alloc, sizeof(clause_block_t));
    if (clause_blocks == NULL)
	err_printf(__cfunc__, "Couldn't allocate space for clause blocks\n");	
    clause_block_count = 1;
    clause_blocks[clause_block_count-1].start_id = 1;
    clause_blocks[clause_block_count-1].length = 0;
    clause_blocks[clause_block_count-1].chunk = ilist_new(MIN_SIZE);
    clause_blocks[clause_block_count-1].offset = ilist_new(MIN_SIZE);
    clause_xvar_reference = ilist_new(MIN_SIZE);
    clause_defining_start_id = ilist_new(MIN_SIZE);
    clause_defining_end_id = ilist_new(MIN_SIZE);
}

/* Return -1, 0, or +1 depending on whether clause is below, within, or beyond block */
int clause_probe_block(int bid, int cid) {
    int pos = cid - clause_blocks[bid].start_id;
    if (pos < 0)
	return -1;
    if (pos >= clause_blocks[bid].length)
	return +1;
    return 0;
}

/* Return pointer to beginning of clause within block */
int *clause_locate_within(int bid, int cid) {
    int pos = cid - clause_blocks[bid].start_id;
    int chunk = clause_blocks[bid].chunk[pos];
    int offset = clause_blocks[bid].offset[pos];
    if (offset < 0)
	return NULL;
    return chunk_set[chunk] + offset;
}

/* Return pointer to beginning of any existing clause */
int *clause_locate(int cid) {
    int bid;
    /* Ensure that lid <= bid <= rid */
    int lid = 0;
    int rid = clause_block_count - 1;
    while (lid <= rid) {
	bid = (lid + rid)/2;
	int sense = clause_probe_block(bid, cid);
	if (sense < 0)
	    rid = bid-1;
	else if (sense > 0)
	    lid = bid+1;
	else
	    return clause_locate_within(bid, cid);
    }
    return NULL;
}

/* Record range of defining clause IDs */
void clause_add_defining(int start_cid, int end_cid) {
    int len = ilist_length(clause_defining_start_id);
    if (len == 0 || clause_defining_end_id[len-1] < start_cid - 1) {
	clause_defining_start_id = ilist_push(clause_defining_start_id, start_cid);
	clause_defining_end_id = ilist_push(clause_defining_end_id, end_cid);
    } else {
	clause_defining_end_id[len-1] = end_cid;
    }
}

/* Return -1, 0, or +1 depending on whether clause ID is below,
   within, or beyond indicated range */
int clause_probe_range(int idx, int cid) {
    int start_id = clause_defining_start_id[idx];
    int end_id = clause_defining_end_id[idx];
    if (cid < start_id)
	return -1;
    if (cid > end_id)
	return +1;
    return 0;
}

/* Is this the ID of a defining clause? */
bool is_defining(int cid) {
    int len = ilist_length(clause_defining_start_id);
    if (len <= 0)
	return false;
    int ridx = len-1;
    int lidx = 0;
    while (lidx <= ridx) {
	int idx = (lidx + ridx)/2;
	int sense = clause_probe_range(idx, cid);
	if (sense == 0)
	    return true;
	if (sense < 0) {
	    ridx = idx-1;
	} else { 
	    // sense > 0
	    lidx = idx + 1;
	}
    }
    return false;
}

bool clause_delete(int cid) {
    int bid;
    int lid = 0;
    int rid = clause_block_count - 1;
    /* Ensure that lid <= bid <= rid */
    while (lid <= rid) {
	bid = (lid + rid)/2;
	int sense = clause_probe_block(bid, cid);
	if (sense < 0)
	    rid = bid-1;
	else if (sense > 0)
	    lid = bid+1;
	else {
	    int pos = cid - clause_blocks[bid].start_id;
	    int chunk = clause_blocks[bid].chunk[pos];
	    int offset = clause_blocks[bid].offset[pos];
	    bool deleting = offset >= 0;
	    if (deleting) {
		int *loc = chunk_set[chunk] + offset;
		while (*loc) {
		    int lit = *loc++;
		    int var = IABS(lit);
		    if (var > input_variable_count) {
			if (var > variable_limit)
			    err_printf(__cfunc__, "Deleting clause with literal %d.  Exceeds variable limit of %d\n", lit, variable_limit);
			clause_xvar_reference[var-input_variable_count-1] --;
		    }
		}
	    }
	    clause_blocks[bid].chunk[pos] = -1;
	    clause_blocks[bid].offset[pos] = -1;
	    return deleting;
	}
    }
    return false;
}

void start_clause(int cid) {
    if (clause_last_id == 0)
	clause_init();
    if (clause_locate(cid) != NULL)
	err_printf(__cfunc__, "Can't add clause %d.  Clause Id already defined\n", cid);
    if (cid < clause_last_id)
	err_printf(__cfunc__, "Can't add clause %d.  Already added higher numbered clause %d\n", cid, clause_last_id);
    if (cid > clause_last_id + MAX_GAP) {
	/* Need to start new block */
	if (clause_block_count == clause_block_alloc) {
	    /* Need more blocks */
	    clause_block_alloc = (int) (clause_block_alloc * GROW_RATIO);
	    clause_blocks = realloc(clause_blocks, clause_block_alloc * sizeof(clause_block_t));
	    if (clause_blocks == NULL)
		err_printf(__cfunc__, "Failed to add enough clause blocks for %d blocks\n", clause_block_alloc);
	}
	clause_block_count++;
	info_printf(3, "Starting new clause block.  Id = %d\n", cid);
	clause_blocks[clause_block_count-1].start_id = cid;
	clause_blocks[clause_block_count-1].length = 0;
	clause_blocks[clause_block_count-1].chunk = ilist_new(MIN_SIZE);
	clause_blocks[clause_block_count-1].offset = ilist_new(MIN_SIZE);
    } else {
	/* Fill in with null clauses */
	int ncid;
	for (ncid = clause_last_id+1; ncid < cid; ncid++) {
	    clause_blocks[clause_block_count-1].chunk = ilist_push(clause_blocks[clause_block_count-1].chunk, -1);
	    clause_blocks[clause_block_count-1].offset = ilist_push(clause_blocks[clause_block_count-1].offset, -1);
	    clause_blocks[clause_block_count-1].length ++;
	}
    }
    clause_last_id = cid;
    clause_count ++;
    current_clause = ilist_resize(current_clause, 0);
    info_printf(3, "Starting clause %d\n", cid);
}

/* Save the current clause */
void finish_clause(int cid) {
    long int need = ilist_length(current_clause);
    if (need > CHUNK_SIZE) {
	err_printf("finish_clause", "Attempt to save clause of length %d.  Max allowed length = %d\n", ilist_length(current_clause), CHUNK_SIZE);
	exit(1);
    }
    if (need + chunk_used > CHUNK_SIZE) {
	// Must start new chunk
	if (chunk_count >= CHUNK_MAX-1)
	    err_printf(__cfunc__, "Reached maximum of %d chunks\n", CHUNK_MAX);	
	chunk_set[chunk_count] = calloc(CHUNK_SIZE, sizeof(int));
	if (chunk_set[chunk_count] == NULL)
	    err_printf(__cfunc__, "Couldn't allocate space for clause chunk %d\n", chunk_count);	
	chunk_count++;
	chunk_used = 0;
    }
    int pos = chunk_used;
    memcpy(chunk_set[chunk_count-1] + chunk_used, current_clause, ilist_length(current_clause) * sizeof(int));
    chunk_used += ilist_length(current_clause);
    // Record clause position
    clause_blocks[clause_block_count-1].chunk = ilist_push(clause_blocks[clause_block_count-1].chunk, chunk_count-1);
    clause_blocks[clause_block_count-1].offset = ilist_push(clause_blocks[clause_block_count-1].offset, pos);
    clause_blocks[clause_block_count-1].length ++;
    info_printf(3, "Finished clause.  Full length %d.  Chunk ID %d.  Offset %d ", need, chunk_count-1, pos);
    if (verb_level >= 3) 
	clause_show(stdout, cid, true);
}

/* Add either literal or terminating 0 to current clause */
void clause_add_literal(int lit) { 
    current_clause = ilist_push(current_clause, lit);
    int var = IABS(lit);
    if (var > input_variable_count) {
	if (var > variable_limit)
	    err_printf(__cfunc__, "Adding clause with literal %d.  Exceeds variable limit of %d\n", lit, variable_limit);
	clause_xvar_reference[var-input_variable_count-1] ++;
    }
}

bool clause_is_unit(int *lits) {
    /* Can have multiple repetitions of single literal */
    if (lits == NULL || lits[0] == 0)
	return false;
    int lit = lits[0];
    int i;
    for (i = 1; lits[i] == lit; i++)
	;
    return lits[i] == 0;
}

void clause_show(FILE *out, int cid, bool endline) {
    int *loc = clause_locate(cid);
    if (loc == NULL) {
	return;
    } 
    fprintf(out, "%d:", cid);
    while (*loc != 0) {
	fprintf(out, " %d", *loc);
	loc++;
    }
    if (endline)
	fprintf(out, "\n");
}

void clause_show_all(FILE *out) {
    int bid;
    for (bid = 0; bid < clause_block_count; bid++) {
	int i;
	for (i = 0; i < clause_blocks[bid].length; i++) {
	    clause_show(out, clause_blocks[bid].start_id + i, true);
	}
    }
}

/*============================================
  RUP
============================================*/

#define RUP_CONFLICT INT_MAX
#define RUP_STALL 0

/* Initialize lset to complement of literals */
/* Return false if encounter conflict */
bool rup_setup(int *lits) {
    lset_clear();
    int lit;
    while ((lit = *lits) != 0) {
	if (!lset_add_lit(-lit))
	    return false;
	lits++;
    }
    return true;
}

int rup_unit_prop(int cid) {
    int *lits = clause_locate(cid);
    if (lits == NULL)
	err_printf(__cfunc__, "Clause #%d deleted or never existed\n", cid);
    int unit = RUP_CONFLICT;
    int lit;
    while ((lit = *lits) != 0) {
	lits++;
	if (lit == unit) 
	    /* Repeated unit literal */
	    continue;
	int var = IABS(lit);
	int rlit = lset_get_lit(var);
	if (rlit == lit)
	    return RUP_STALL;
	else if (rlit == -lit)
	    continue;
	else if (unit == RUP_CONFLICT)
	    unit = lit;
	else
	    return RUP_STALL;
    }
    return unit;
}

/* Run RUP on hints from file.  Assume already set up  */
void rup_run(int tcid, bool defining_only) {
    bool conflict = false;
    int steps = 0;
    while (true) {
	token_t token = token_next();
	if (token == TOK_STAR)
	    err_printf(__cfunc__, "This checker requires explicit hints\n");
	else if (token != TOK_INT)
	    err_printf(__cfunc__, "RUP for clause %d.  Expecting integer hint.  Got %s ('%s') instead\n", tcid, token_name[token], token_last);
	else if (token_value == 0) {
	    if (!conflict)
		err_printf(__cfunc__, "RUP failure for clause %d.  Didn't have conflict on final clause\n", tcid);
	    info_printf(3, "RUP for clause %d.  Succeeded in %d steps\n", tcid, steps);
	    return;
	} else {
	    if (conflict) {
		if (early_rup) {
		    while (token_value != 0) {
			token = token_next();
			if (token != TOK_INT)
			    err_printf(__cfunc__, "RUP for clause %d.  Expecting integer hint.  Got %s ('%s') instead\n", tcid, token_name[token], token_last);
		    }
		    info_printf(3, "RUP for clause %d.  Succeeded in %d steps\n", tcid, steps);
		    return;
		} else
		    err_printf(__cfunc__, 
			       "RUP failure for clause %d.  Encountered conflict after processing %d hints.  Not at end of hints list\n", tcid, steps);
	    }
	    int cid = token_value;
	    if (defining_only && !is_defining(cid)) 
		err_printf(__cfunc__, "RUP for clause %d.  Hint %d is not from a defining clause\n", tcid, cid);
	    int unit = rup_unit_prop(cid);
	    steps ++;
	    if (unit == RUP_CONFLICT)
		conflict = true;
	    else if (unit == RUP_STALL) {
		fprintf(ERROUT, "FAILURE: Clause %d did not cause unit propagation\n", cid);
		if (verb_level >= 2) {
		    fprintf(ERROUT, "    Added literals: ");
		    lset_show(ERROUT);
		    fprintf(ERROUT, "\n    Clause ");
		    clause_show(ERROUT, cid, true);
		}
		err_printf(__cfunc__, "RUP failure for clause %d\n", tcid);
	    } else
		lset_add_lit(unit);
	}
    }
}

/* Skip over RUP hints in file.  Assume already set up  */
void rup_skip(int tcid) {
    while (true) {
	token_t token = token_next();
	if (token == TOK_STAR)
	    continue;
	else if (token != TOK_INT)
	    continue;
	else if (token_value == 0)
	    return;
    }
}


/*============================================
  Processing files
============================================*/

void cnf_read(char *fname) {
    token_setup(fname);
    /* Find and parse header */
    while (true) {
	token_t token = token_next();
	if (token == TOK_EOL)
	    continue;
	if (token != TOK_STRING)
	    err_printf(__cfunc__, "Unexpected token %s ('%s') while looking for CNF header\n", token_name[token], token_last);
	if (token_last[0] == 'c')
	    token_find_eol();
	else if (token_last[0] == 'p') {
	    if (token_last[1] != '\0')
		err_printf(__cfunc__, "Invalid CNF field %s ('%s')\n", token_name[token], token_last);
	    token = token_next();
	    if (strcmp(token_last, "cnf") != 0)
		err_printf(__cfunc__, "Expected field 'cnf'.  Got %s ('%s')\n", token_name[token], token_last);
	    token = token_next();
	    if (token != TOK_INT)
		err_printf(__cfunc__, "Invalid CNF variable count %s ('%s')\n", token_name[token], token_last);
	    input_variable_count = token_value;
	    variable_limit = input_variable_count;
	    token = token_next();
	    if (token != TOK_INT)
		err_printf(__cfunc__, "Invalid CNF clause count %s ('%s')\n", token_name[token], token_last);
	    input_clause_count = token_value;
	    token = token_next();
	    if (token != TOK_EOL)
		err_printf(__cfunc__, "Invalid field in CNF header %s ('%s')\n", token_name[token], token_last);
	    break;
	} else
	    err_printf(__cfunc__, "Unexpected token %s ('%s') while reading CNF header\n", token_name[token], token_last);
    }
    /* Read clauses */
    int found_clause_count = 0;
    bool within_clause = false;
    int last_literal = INT_MAX;
    while (true) {
	token_t token = token_next();
	if (token == TOK_EOF)
	    break;
	else if (token == TOK_EOL)
	    continue;
	else if (token == TOK_STRING && token_last[0] == 'c')
	    token_find_eol();
	else if (token == TOK_EOL)
	    continue;
	else if (token == TOK_INT) {
	    if (!within_clause) {
		start_clause(found_clause_count+1);
		within_clause = true;
		last_literal = INT_MAX;
	    }
	    clause_add_literal(token_value);
	    last_literal = token_value;
	    if (token_value == 0) {
		found_clause_count ++;
		within_clause = false;
		finish_clause(found_clause_count);
	    }
	}
	else
	    err_printf(__cfunc__, "Unexpected token %s ('%s') found in CNF file\n", token_name[token], token_last);
    }
    if (found_clause_count != input_clause_count)
	err_printf(__cfunc__, "Invalid CNF.  Expected %d clauses.  Found %d\n", input_clause_count, found_clause_count);
    token_finish();
    data_printf(1, "Read CNF file with %d variables and %d clauses\n", input_variable_count, input_clause_count);
}

void cnf_show(FILE *out) {
    int cid;
    if (verb_level < 1)
	return;
    printf("CNF File.  %d clauses\n", input_clause_count);
    for (cid = 1; cid <= input_clause_count; cid++) {
	clause_show(out, cid, true);
    }
}

typedef enum {NODE_PRODUCT, NODE_SUM, NODE_NONE} node_type_t;

/* Representation of POG node */
typedef struct {
    node_type_t type;
    int id;                 /* Node ID */
    int cid;                /* First defining clause ID */
    ilist dependency_list;  /* All variables in subgraph */
    ilist children;         /* Node IDs of children */
    q25_ptr ring_value;     /* For counting */
} node_t;

node_t *node_list = NULL;
int node_asize = 0;
int node_count = 0;
int node_deleted_count = 0;

node_t *node_find(int id) {
    int idx = id - input_variable_count - 1;
    if (idx < 0 || idx >= node_asize)
	return NULL;
    return &node_list[idx];
}

node_t *node_new(node_type_t type, int id, int cid) {
    if (id <= input_variable_count)
	err_printf(__cfunc__, "Invalid operation id %d\n", id);
    if (id-input_variable_count > node_asize) {
	int nasize = id-input_variable_count;
	if (nasize < MIN_SIZE)
	    nasize = MIN_SIZE;
	if (nasize < (int) (GROW_RATIO * node_asize))
	    nasize = (int) (GROW_RATIO * node_asize);
	if (node_list == NULL)
	    node_list = calloc(nasize, sizeof(node_t));
	else
	    node_list = realloc(node_list, nasize * sizeof(node_t));
	if (node_list == NULL)
	    err_printf(__cfunc__, "Couldn't allocate space for node list of size %d\n", nasize);
	int idx;
	for (idx = node_asize; idx < nasize; idx++) {
	    int nid = idx + input_variable_count + 1;
	    node_list[idx].type = NODE_NONE;
	    node_list[idx].id = nid;
	    node_list[idx].cid = 0;
	    node_list[idx].dependency_list = NULL;
	    node_list[idx].children = NULL;
	    clause_xvar_reference = ilist_push(clause_xvar_reference, 0);
	}
	info_printf(3, "Resized node array %d --> %d\n", node_asize, nasize);
	node_asize = nasize;
	variable_limit = node_asize + input_variable_count;
    }
    node_t *node = node_find(id);
    if (node->type != NODE_NONE)
	err_printf(__cfunc__, "Cannot create new node with id %d.  Id already in use\n", id);
    node->type = type;
    node->cid = cid;
    node->ring_value = NULL;
    node_count ++;
    return node;
}

int cpog_operation_count = 0;
int cpog_assertion_count = 0;
int cpog_assertion_deletion_count = 0;
int cpog_operation_clause_count = 0;

void cpog_show(FILE *out) {
    int cid;
    int idx, nid;
    printf("CPOG Operations\n");
    for (idx = 0; idx < node_asize; idx++) {
	nid = input_variable_count + 1 + idx;
	node_t *node = node_find(nid);
	if (node == NULL || node->type == NODE_NONE)
	    continue;
	fprintf(out, "N%d: %s(", nid, node->type == NODE_PRODUCT ? "AND" : "OR");
	ilist_print(node->children, out, ", ");
	fprintf(out, ")\n");
	int n = ilist_length(node->children);
	int i;
	for (i = 0; i <= n; i++) {
	    fprintf(out, "  ");
	    clause_show(out, node->cid + i, true);
	}
    }
}

/* Handlers for different command types.  Each starts after parsing command token */
void cpog_read_root() {
    token_t token = token_next();
    if (token != TOK_INT)
	err_printf(__cfunc__, "Unexpected token %s ('%s')\n", token_name[token], token_last);
    declared_root = token_value;
    info_printf(3, "Root literal declared as %d\n", declared_root);
}

void cpog_add_clause(int cid) {
    lset_clear();
    start_clause(cid);
    while (true) {
	token_t token = token_next();
	if (token != TOK_INT)
	    err_printf(__cfunc__, "Unexpected token %s ('%s')\n", token_name[token], token_last);
	int lit = token_value;
	clause_add_literal(lit);
	if (lit == 0)
	    break;
	else
	    lset_add_lit(-lit);
    }
    finish_clause(cid);
    if (one_sided)
	rup_skip(cid);
    else
	rup_run(cid, false);
    token_confirm_eol();
    cpog_assertion_count ++;
    info_printf(3, "Processed clause %d addition\n", cid);
}

void cpog_delete_clause() {
    /* Before start deletions, lets show what was there */ 
    if (verb_level >= 3 && cpog_assertion_deletion_count == 0) {
	info_printf(3, "Before performing deletions\n");
	cpog_show(stdout);
	printf("All clauses:\n");
	clause_show_all(stdout);
    }
    token_t token = token_next();
    if (token != TOK_INT)
	err_printf(__cfunc__, "Unexpected token %s ('%s')\n", token_name[token], token_last);
    int cid = token_value;
    int *lits = clause_locate(cid);
    bool tautology = !rup_setup(lits);
    bool deleted = clause_delete(cid);
    if (!deleted) 
	err_printf(__cfunc__, "Could not delete clause %d.  Never defined or already deleted\n", cid);
    if (!tautology)
	rup_run(cid, false);
    token_find_eol();
    cpog_assertion_deletion_count ++;
    info_printf(3, "Processed clause %d deletion\n", cid);
}

void cpog_add_product(int cid) {
    token_t token = token_next();
    if (token != TOK_INT)
	err_printf(__cfunc__, "Expected operation number.  Got %s ('%s') instead\n", token_name[token], token_last);
    int nid = token_value;
    node_t *node = node_new(NODE_PRODUCT, nid, cid);
    node->children = ilist_new(2);
    node->dependency_list = ilist_new(1);
    ilist local_dependency_list = ilist_new(0);
    /* Get children */
    while (true) {
	token = token_next();
	if (token != TOK_INT)
	    err_printf(__cfunc__, "Expected product operation argument.  Got %s ('%s') instead\n", token_name[token], token_last);
	if (token_value == 0)
	    break;
	int lit = token_value;
	int var = IABS(lit);
	node->children = ilist_push(node->children, lit);
	if (var <= input_variable_count) {
	    if (ilist_is_member(node->dependency_list, var) || ilist_is_member(local_dependency_list, var))
		err_printf(__cfunc__, "Can't add literal %d to node %d children.  Variable %d already in dependency set\n", lit, nid, var);
	    local_dependency_list = ilist_push(local_dependency_list, var);
	} else {
	    node_t *cnode = node_find(var);
	    if (cnode == NULL || cnode->type == NODE_NONE) 
		err_printf(__cfunc__, "Can't add literal %d to node %d children.  Invalid node Id %d\n", lit, nid, var);
	    if (!ilist_is_disjoint(node->dependency_list, cnode->dependency_list) ||
		!ilist_is_disjoint(local_dependency_list, cnode->dependency_list)) 
		err_printf(__cfunc__, "Can't add literal %d to node %d children.  Overlapping dependency sets\n", lit, nid);
	    ilist save = node->dependency_list;
	    node->dependency_list = ilist_union(node->dependency_list, cnode->dependency_list);
	    ilist_free(save);
	}
    }
    if (ilist_length(local_dependency_list) > 0) {
	ilist_sort(local_dependency_list);
	ilist save = node->dependency_list;
	node->dependency_list = ilist_union(node->dependency_list, local_dependency_list);
	ilist_free(save);
    }
    ilist_free(local_dependency_list);
    if (ilist_length(node->children) < 2) 
	err_printf(__cfunc__, "Sum node %d has %d childen.  Must have >= 2\n", nid, ilist_length(node->children));

    /* Done */
    token = token_next();
    if (token != TOK_EOL) 
	err_printf(__cfunc__, "Expected end of line.  Got %s ('%s') instead\n", token_name[token], token_last);

    /* Add clauses */
    start_clause(cid);
    clause_add_literal(nid);
    int i;
    int n = ilist_length(node->children);
    for (i = 0; i < n; i++)
	clause_add_literal(-node->children[i]);
    clause_add_literal(0);
    finish_clause(cid);
    for (i = 0; i < n; i++) {
	start_clause(cid+i+1);
	clause_add_literal(-nid);
	clause_add_literal(node->children[i]);
	clause_add_literal(0);
	finish_clause(cid+i+1);
    }
    clause_add_defining(cid, cid+n+1);
    cpog_operation_count ++;
    cpog_operation_clause_count += (n+1);
    info_printf(3, "Processed product %d addition\n", nid);
}

void cpog_add_sum(int cid) {
    token_t token = token_next();
    if (token != TOK_INT)
	err_printf(__cfunc__, "Expected operation number.  Got %s ('%s') instead\n", token_name[token], token_last);
    int nid = token_value;
    node_t *node = node_new(NODE_SUM, nid, cid);
    node->children = ilist_new(2);
    node->dependency_list = ilist_new(1);
    ilist local_dependency_list = ilist_new(0);
    /* Get children */
    while (true) {
	token = token_next();
	if (token != TOK_INT) 
	    err_printf(__cfunc__, "Expected sum operation argument.  Got %s ('%s') instead\n", token_name[token], token_last);
	int lit = token_value;
	int var = IABS(lit);
	node->children = ilist_push(node->children, lit);
	if (var <= input_variable_count) {
	    local_dependency_list = ilist_push(local_dependency_list, var);
	} else {
	    node_t *cnode = node_find(var);
	    if (cnode == NULL || cnode->type == NODE_NONE)
		err_printf(__cfunc__, "Can't add literal %d to node %d children.  Invalid node Id %d\n", lit, nid, var);
	    ilist save = node->dependency_list;
	    node->dependency_list = ilist_union(node->dependency_list, cnode->dependency_list);
	    ilist_free(save);
	}
	if (ilist_length(node->children) == 2)
	    break;
    }
    if (ilist_length(local_dependency_list) > 0) {
	ilist_sort(local_dependency_list);
	ilist save = node->dependency_list;
	node->dependency_list = ilist_union(node->dependency_list, local_dependency_list);
	ilist_free(save);
    }
    ilist_free(local_dependency_list);
    
    /* Prove mutual exclusion */
    lset_clear();
    lset_add_lit(node->children[0]);
    lset_add_lit(node->children[1]);
    rup_run(cid, true);

    token_confirm_eol();
    /* Add sum clause */
    start_clause(cid);
    clause_add_literal(-nid);
    int i;
    int n = ilist_length(node->children);
    for (i = 0; i < n; i++)
	clause_add_literal(node->children[i]);
    clause_add_literal(0);
    finish_clause(cid);
    for (i = 0; i < n; i++) {
	start_clause(cid+i+1);
	clause_add_literal(nid);
	clause_add_literal(-node->children[i]);
	clause_add_literal(0);
	finish_clause(cid+i+1);
    }
    clause_add_defining(cid, cid+n+1);
    cpog_operation_count ++;
    cpog_operation_clause_count += (n+1);
    info_printf(3, "Processed sum %d addition\n", nid);
}

void cpog_delete_operation() {
    token_t token = token_next();
    if (token != TOK_INT)
	err_printf(__cfunc__, "Expecting integer operation ID.  Got %s ('%s') instead\n", token_name[token], token_last);
    int id = token_value;
    node_t *node = node_find(id);
    if (node == NULL || node->type == NODE_NONE) 
	err_printf(__cfunc__, "Cannot delete operation #%d.  Already deleted or never defined\n", id);
    int i;
    for (i = 0; i <= ilist_length(node->children); i++) {
	int cid = node->cid + i;
	if (!clause_delete(cid)) 
	    err_printf(__cfunc__, "Cannot delete operation #%d.  Defining clause #%d never defined or already deleted\n", id, cid);
    }
    int refs = clause_xvar_reference[id-input_variable_count-1];
    if (refs != 0) 
	err_printf(__cfunc__, "Cannot delete operation #%d.  %d clauses still contain reference to it\n", id, refs);
    node->type = NODE_NONE;
    node_count --;
    node_deleted_count ++;
    info_printf(3, "Processed operation %d deletion\n", id);
}

/* Check end condition.  Return literal representation of root node */
int cpog_final_root() {
    /* First delete all of the clauses added for operations */
    int idx, nid, i;
    int root = 0;
    for (idx = 0; idx < node_asize; idx++) {
	nid = input_variable_count + idx + 1;
	node_t *node = node_find(nid);
	if (node == NULL || node->type == NODE_NONE)
	    continue;
	int n = ilist_length(node->children);
	for (i = 0; i <= n; i++)
	    clause_delete(node->cid + i);
    }
    int bid;
    for (bid = 0; bid < clause_block_count; bid++) {
	for (i = 0; i < clause_blocks[bid].length; i++) {
	    int cid = clause_blocks[bid].start_id + i;
	    int *lits = clause_locate(cid);
	    if (lits != NULL) {
		if (clause_is_unit(lits)) {
		    if (root == 0)
			root = *lits;
		    else 
			err_printf(__cfunc__, "Found at least two root literals: %d and %d\n", root, *lits);
		} else 
		    err_printf(__cfunc__, "Found undeleted, non-unit clause #%d\n", cid);
	    }
	}
    }
    if (root == 0) 
	err_printf(__cfunc__, "Didn't find root node\n");
    if (declared_root != 0 && declared_root != root) 
	err_printf(__cfunc__, "Declared root node %d doesn't match remaining unit literal %d\n", declared_root, root);

    return root;
}

void cpog_read(char *fname) {
    token_setup(fname);
    /* Find and parse each command */
    while (true) {
	int cid = 0;
	token_t token = token_next();
	if (token == TOK_EOF)
	    break;
	if (token == TOK_EOL)
	    continue;
	if (token == TOK_STRING && token_last[0] == 'c') {
	    token_find_eol();
	    continue;
	} else if (token == TOK_INT) {
	    cid = token_value;
	    token = token_next();
	} 
	if (token != TOK_STRING) 
	    err_printf(__cfunc__, "Expecting CPOG command.  Got %s ('%s') instead\n", token_name[token], token_last);
	else if (strcmp(token_last, "a") == 0)
	    cpog_add_clause(cid);
	else if (strcmp(token_last, "r") == 0)
	    cpog_read_root();
	else if (strcmp(token_last, "dc") == 0 || strcmp(token_last, "d") == 0)
	    cpog_delete_clause();
 	else if (strcmp(token_last, "p") == 0)
	    cpog_add_product(cid);
	else if (strcmp(token_last, "s") == 0)
	    cpog_add_sum(cid);
	else if (strcmp(token_last, "do") == 0)
	    cpog_delete_operation();
	else 
	    err_printf(__cfunc__, "Invalid CPOG command '%s'\n", token_last);
    }
    token_finish();
    int all_clause_count = cpog_assertion_count + cpog_operation_clause_count;
    data_printf(1, "Read CPOG file with %d operations,  %d asserted + %d defining = %d clauses\n",
		cpog_operation_count, cpog_assertion_count,
		cpog_operation_clause_count, all_clause_count);
    data_printf(3, "Clauses divided into %d blocks\n", clause_block_count);
    data_printf(1, "Deleted %d input and asserted clauses\n", cpog_assertion_deletion_count);
}

/*============================================
  Counting
============================================*/

q25_ptr *input_weights = NULL;
q25_ptr rescale = NULL;

/* Perform ring evalation.
   Given array of weights for input variables
*/
q25_ptr ring_evaluate(q25_ptr *input_weights) {
    int id;
    q25_ptr val;
    printf("Root ID = %d\n", declared_root);
    for (id = input_variable_count+1; id <= declared_root; id++) {
	node_t *np = node_find(id);
	val = q25_from_32(np->type == NODE_PRODUCT ? 1 : 0);
	int i;
	for (i = 0; i < ilist_length(np->children); i++) {
	    int clit = np->children[i];
	    int cid = IABS(clit);
	    q25_ptr cval;
	    if (cid <= input_variable_count) 
		cval = input_weights[cid-1];
	    else {
		node_t *cnp = node_find(cid);
		cval = cnp->ring_value;
	    }
	    if (clit < 0)
		cval = q25_one_minus(cval);
	    q25_ptr nval = np->type == NODE_PRODUCT ? q25_mul(val, cval) : q25_add(val, cval);
	    q25_free(val);
	    if (clit < 0)
		q25_free(cval);
	    val = nval;
	}
	np->ring_value = val;
	if (verb_level >= 3) {
	    info_printf(3, "Ring value for node %d: ", np->id);
	    q25_write(val, stdout);
	    printf("\n");
	}
    }
    val = q25_copy(val);
    for (id = input_variable_count+1; id <= declared_root; id++) {
	node_t *np = node_find(id);
	q25_free(np->ring_value);
	np->ring_value = NULL;
    }
    return val;
}

q25_ptr count_regular() {
    q25_ptr *input_weights = calloc(input_variable_count, sizeof(q25_ptr));
    if (input_weights == NULL) {
	err_printf("count_regular", "Couldn't allocate memory for weights\n");
	return NULL;
    }
    q25_ptr qone = q25_from_32(1);
    q25_ptr half = q25_scale(qone, -1, 0);
    q25_free(qone);
    int v;
    for (v = 1; v <= input_variable_count; v++)
	input_weights[v-1] = half;
    q25_ptr density = ring_evaluate(input_weights);
    q25_ptr result = q25_scale(density, input_variable_count, 0);
    q25_free(half);
    q25_free(density);
    free(input_weights);
    return result;
}


bool cnf_read_weights(char *fname) {
    bool found_wmc = false;
    token_setup(fname);
    /* Find and parse wmc header */
    while (true) {
	token_t token = token_next();
	if (token == TOK_EOL)
	    continue;
	if (token != TOK_STRING)
	    err_printf(__cfunc__, "Unexpected token %s ('%s') while looking for WMC header\n", token_name[token], token_last);
	if (token_last[0] == 'c') {
	    if (!found_wmc) {
		bool ok = true;
		token = token_next();
		ok = token == TOK_STRING && strcmp(token_last, "t") == 0;
		if (ok)
		    token = token_next();
		ok = ok && token == TOK_STRING && strcmp(token_last, "wmc") == 0;
		if (ok)
		    found_wmc = true;
	    }
	    if (token != TOK_EOL)
		token_find_eol();
	} else if (token_last[0] == 'p') {
	    if (found_wmc) {
		token_find_eol();
		break;
	    }
	    else {
		/* Not weighted model counting problem */
		token_finish();
		return false;
	    }
	}
    }
    input_weights = calloc(input_variable_count, sizeof(q25_ptr));
    q25_ptr *positive_weights = calloc(input_variable_count, sizeof(q25_ptr));
    q25_ptr *negative_weights = calloc(input_variable_count, sizeof(q25_ptr));
    if (!input_weights || !positive_weights || !negative_weights) 
	err_printf(__cfunc__, "Couldn't allocate memory for weights\n");
    rescale = q25_from_32(1);
    while (true) {
	token_t token = token_next();
	if (token == TOK_EOF)
	    break;
	else if (token == TOK_EOL)
	    continue;
	else if (token == TOK_STRING && token_last[0] == 'c') {
	    bool ok = true;
	    token = token_next();
	    ok = token == TOK_STRING && strcmp(token_last, "p") == 0;
	    if (ok)
		token = token_next();
	    ok = ok && token == TOK_STRING && strcmp(token_last, "weight") == 0;
	    if (ok)
		token = token_next();
	    ok = ok && token == TOK_INT;
	    ok = ok && skip_space();
	    if (!ok) {
		if (token != TOK_EOL)
		    token_find_eol();
		continue;
	    }
	    int lit = token_value;
	    int var = IABS(lit);

	    if (var > input_variable_count)
		err_printf(__cfunc__, "Invalid literal %d for weight\n", lit);
	    q25_ptr cur_val = lit < 0 ? negative_weights[var-1] : positive_weights[var-1];
	    if (cur_val != NULL)
		err_printf(__cfunc__, "Already have weight for literal %d\n", lit);
	    q25_ptr val = q25_read(token_file);
	    ok = q25_is_valid(val);
	    if (ok)
		token = token_next();
	    ok = ok && token == TOK_INT && token_value == 0;
	    if (!ok)
		err_printf(__cfunc__, "Couldn't read weight for literal %d\n", lit);
	    token_find_eol();
	    if (lit < 0)
		negative_weights[var-1] = val;
	    else
		positive_weights[var-1] = val;
	    info_printf(3, "Found weight for literal %d\n", lit);
	} else
	    token_find_eol();
    }
    token_finish();
    /* Fix up weights */
    int var;
    for (var = 1; var <= input_variable_count; var++) {
	q25_ptr pwt = positive_weights[var-1];
	q25_ptr nwt = negative_weights[var-1];
	if (nwt == NULL) {
	    if (pwt == NULL)
		err_printf(__cfunc__, "No weight assigned to either literal of variable %d\n", var);
	    else
		input_weights[var-1] = pwt;
	} else if (pwt == NULL) {
	    input_weights[var-1] = q25_one_minus(nwt);
	    q25_free(nwt);
	} else {
	    q25_ptr sum = q25_add(nwt, pwt);
	    if (q25_is_one(sum)) {
		input_weights[var-1] = pwt;
		q25_free(nwt); q25_free(sum);
	    } else {
		q25_ptr recip = q25_recip(sum);
		if (!q25_is_valid(recip))
		    err_printf(__cfunc__, "Could not get reciprocal of summed weights for variable %d\n", var);
		q25_ptr nrescale = q25_mul(rescale, sum);
		q25_free(rescale);
		rescale = nrescale;
		input_weights[var-1] = q25_mul(pwt, recip);
		q25_free(nwt); q25_free(pwt);
		q25_free(sum); q25_free(recip);
	    }
	}
    }
    free(positive_weights);
    free(negative_weights);
    data_printf(2, "Read weights from CNF file\n", input_variable_count, input_clause_count);
    return true;
}

q25_ptr count_weighted(char *fname) {
    if (!cnf_read_weights(fname))
	return NULL;
    q25_ptr val = ring_evaluate(input_weights);
    q25_ptr rval = q25_mul(val, rescale);
    q25_free(val);
    q25_free(rescale);
    int v;
    for (v = 1; v < input_variable_count; v++) {
	q25_free(input_weights[v-1]);
    }
    free(input_weights);
    return rval;
}

void run(char *cnf_name, char *cpog_name) {
    double start = tod();
    cnf_read(cnf_name);
    if (verb_level >= 3)
	cnf_show(stdout);
    if (cpog_name != NULL) {
	cpog_read(cpog_name);
	if (verb_level >= 3) {
	    cpog_show(stdout);
	    printf("All clauses:\n");
	    clause_show_all(stdout);
	}
	int root = cpog_final_root();
	data_printf(1, "Final root literal %d\n", root);
	if (one_sided)
	    data_printf(0, "ONE-SIDED VALID.  CPOG representation partially verified\n");
	else
	    data_printf(0, "FULL-PROOF SUCCESS.  CPOG representation verified\n");
    }
    double post_check = tod();
    q25_ptr mc = count_regular();
    if (mc && q25_is_valid(mc)) {
	data_printf(0, "Regular model count = ");
	q25_write(mc, stdout);
	printf("\n");
    }
    q25_free(mc);
    q25_ptr wmc = count_weighted(cnf_name);
    if (wmc && q25_is_valid(wmc)) {
	data_printf(0, "Weighted model count = ");
	q25_write(wmc, stdout);
	printf("\n");
    }
    q25_free(wmc);
    double secs = tod() - post_check;
    data_printf(1, "Time to compute model counts: %.3f\n", secs);
    secs = tod() - start;
    data_printf(1, "Elapsed seconds: %.3f\n", secs);
}

int main(int argc, char *argv[]) {
    char *cnf_name = NULL;
    char *cpog_name = NULL;
    verb_level = 1;
    if (argc <= 1) 
	usage(argv[0]);
    int argi;
    char *istring;
    for (argi = 1; argi < argc && argv[argi][0] == '-'; argi++) {
	switch (argv[argi][1]) {
	case 'h':
	    usage(argv[0]);
	    break;
	case 'v':
	    istring = argv[++argi];
	    verb_level = atoi(istring);
	    break;
	case '1':
	    one_sided = true;
	    break;
	default:
	    printf("Unknown command line option '%s'\n", argv[argi]);
	    usage(argv[0]);
	}
    }
    if (argi == argc) {
	printf("Require CNF file\n");
	usage(argv[0]);
    }
    cnf_name = argv[argi++];
    if (argi < argc) {
	cpog_name = argv[argi++];
    }
    run(cnf_name, cpog_name);
    return 0;
}
