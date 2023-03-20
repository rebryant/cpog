/*========================================================================
  Copyright (c) 2023 Randal E. Bryant, Carnegie Mellon University
  
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


#pragma once

#include <stdio.h>
#include <stdarg.h>
#include <stdbool.h>
#include <sys/time.h>

/* Default reporting level.  Must recompile when change */
#ifndef RPT
#define RPT 2
#endif

/* Ways to report interesting behavior and errors */

/* Buffer sizes */
#define MAX_CHAR 512

/* Allow this headerfile to define C++ constructs if requested */
#ifdef __cplusplus
#define CPLUSPLUS
#endif

#ifdef CPLUSPLUS
extern "C" {
#endif

// Time of day for wall clock timing. Measured in seconds
extern double tod();

// Start recording elapsed time
void start_timer();

// Get elapsed time since timer started
double get_elapsed();

extern int verblevel;
void set_verblevel(int level);

typedef void (*panic_function_t)(void);

void set_panic(panic_function_t fun);

extern FILE *errfile;
extern FILE *verbfile;

// Record all information in separate file.  Opens and closes with each write
// so that will be preserved even if process terminates due to segfault or kill
void set_logname(const char *fname);

/* Report Errors */
void err(bool fatal, const char *fmt, ...);
/* Report useful information */
void report(int verblevel, const char *fmt, ...);

/* Like printf, but also records to log file */
void lprintf(const char *fmt, ...);

// Copy string to allocated space
const char *archive_string(const char *tstring);

// Record data entry in logfile
void log_data(const char *fmt, ...);


#ifdef CPLUSPLUS
}
#endif


/* EOF */

