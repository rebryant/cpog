/*========================================================================
  Copyright (c) 2022, 2023 Randal E. Bryant, Carnegie Mellon University
  
  Permission is hereby granted, free of charge, to any person
  obtaining a copy of this software and associated documentation files
  (the "Software"), to deal in the Software without restriction,
  including without limitation the rights to use, copy, modify, merge,
  publish, distribute, sublicense, and/or sell copies of the Software,
  and to permit persons to whom the Software is furnished to do so,
  subject to the following conditions:
  
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

// Turn POG assertions into LRAT
//#define LRAT


#include <string.h>
#include <stdlib.h>
#include "report.h"
#include "ilist.h"
#include "writer.hh"


/// Generic Writer

Writer::Writer(const char *fname) {
    const char *file_name = archive_string(fname);
    line_count = 0;
    outfile = fopen(file_name, "w");
    if (outfile == NULL) {
	err(false, "Couldn't open output file '%s'\n", fname);
    }
}

Writer::Writer() {
    file_name = NULL;
    line_count = 0;
    outfile = stdout;
}

void Writer::enable_comments() {
    do_comments = true;
}

void Writer::comment(const char *fmt, ...) {
    if (!do_comments)
	return;
    va_list ap;
    va_start(ap, fmt);
    fprintf(outfile, "c ");
    vfprintf(outfile, fmt, ap);
    fprintf(outfile, "\n");
    line_count++;
    fflush(outfile);
    va_end(ap);
}

void Writer::write_text(const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    vfprintf(outfile, fmt, ap);
    va_end(ap);
}

void Writer::start_line() {
}

void Writer::add_int(int v) {
    write_text("%d ", v);
}
void Writer::add_text(const char *txt) {
    write_text("%s", txt);
}

void Writer::write_list(ilist vals) {
    for (int i = 0; i < ilist_length(vals); i++)
	add_int(vals[i]);
    add_int(0);
}

void Writer::write_vector(std::vector<int> &vec) {
    for (int v : vec)
	add_int(v);
    add_int(0);
}

void Writer::comment_list(const char *descr, ilist vals) {
    if (!do_comments || ilist_length(vals) == 0)
	return;
    fprintf(outfile, "c %s %d: ", descr, vals[0]);
    for (int i = 1; i < ilist_length(vals); i++)
	add_int(vals[i]);
    add_int(0);
    fprintf(outfile, "\n");
}

void Writer::comment_container(const char *descr, std::vector<int> &vals) {
    if (!do_comments)
	return;
    fprintf(outfile, "c %s: ", descr);
    for (int val : vals)
	add_int(val);
    add_int(0);
    fprintf(outfile, "\n");
}

void Writer::comment_container(const char *descr, std::unordered_set<int> &vals) {
    if (!do_comments)
	return;
    fprintf(outfile, "c %s: ", descr);
    for (int val : vals)
	add_int(val);
    add_int(0);
    fprintf(outfile, "\n");
}

void Writer::comment_container(const char *descr, std::set<int> &vals) {
    if (!do_comments)
	return;
    fprintf(outfile, "c %s: ", descr);
    for (int val : vals)
	add_int(val);
    add_int(0);
    fprintf(outfile, "\n");
}

void Writer::diagnose(const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    vfprintf(stdout, fmt, ap);
    fprintf(stdout, "\n");

    if (!do_comments)
	return;
    va_start(ap, fmt);
    fprintf(outfile, "c ");
    vfprintf(outfile, fmt, ap);
    fprintf(outfile, "\n");
    line_count++;
    fflush(outfile);
    va_end(ap);
}


void Writer::diagnose_list(const char *descr, ilist vals) {
    if (ilist_length(vals) == 0)
	return;
    fprintf(stdout, "c %s %d:", descr, vals[0]);
    for (int i = 1; i < ilist_length(vals); i++)
	fprintf(stdout, " %d", vals[i]);
    fprintf(stdout, " 0\n");

    if (!do_comments)
	return;
    fprintf(outfile, "c %s %d: ", descr, vals[0]);
    for (int i = 1; i < ilist_length(vals); i++)
	add_int(vals[i]);
    add_int(0);
    fprintf(outfile, "\n");
}

void Writer::diagnose_container(const char *descr, std::vector<int> &vals) {
    fprintf(stdout, "c %s:", descr);
    for (int val : vals)
	fprintf(stdout, " %d", val);
    fprintf(stdout, " 0\n");

    if (!do_comments)
	return;
    fprintf(outfile, "c %s: ", descr);
    for (int val : vals)
	add_int(val);
    add_int(0);
    fprintf(outfile, "\n");
}

void Writer::diagnose_container(const char *descr, std::unordered_set<int> &vals) {
    fprintf(stdout, "c %s:", descr);
    for (int val : vals)
	fprintf(stdout, " %d", val);
    fprintf(stdout, " 0\n");

    if (!do_comments)
	return;
    fprintf(outfile, "c %s: ", descr);
    for (int val : vals)
	add_int(val);
    add_int(0);
    fprintf(outfile, "\n");
}

void Writer::diagnose_container(const char *descr, std::set<int> &vals) {
    fprintf(stdout, "c %s:", descr);
    for (int val : vals)
	fprintf(stdout, " %d", val);
    fprintf(stdout, " 0\n");

    if (!do_comments)
	return;
    fprintf(outfile, "c %s: ", descr);
    for (int val : vals)
	add_int(val);
    add_int(0);
    fprintf(outfile, "\n");
}


void Writer::finish_line(const char *txt) {
    write_text("%s\n", txt);
    line_count++;
}

void Writer::finish_file() {
    if (outfile != stdout)
	fclose(outfile);
    outfile = NULL;
    if (file_name == NULL)
	report(2, "%d lines written\n", line_count);
    else
	report(2, "File %s.  %d lines written\n", file_name, line_count);
}

/// Writing CNF files
Cnf_writer::Cnf_writer() : Writer() {}
Cnf_writer::Cnf_writer(const char *fname) : Writer(fname) {}

void Cnf_writer::write_header(int nv, int nc) {
    write_text("p cnf %d %d", nv, nc);
    finish_line("");
}

Pog_writer::Pog_writer() : Writer() {}
Pog_writer::Pog_writer(const char *fname) : Writer(fname) {}

void Pog_writer::declare_root(int root_literal) {
    write_text("r %d", root_literal);
    finish_line("");
}

void Pog_writer::start_assertion(int cid) {
#ifdef LRAT
    write_text("%d ", cid);
#else
    write_text("%d a ", cid);
#endif
}

void Pog_writer::start_and(int cid, int var) {
    write_text("%d p %d ", cid, var);
}

void Pog_writer::start_or(int cid, int var) {
    write_text("%d s %d ", cid, var);
}

void Pog_writer::clause_deletion(std::vector<int> *dvp) {
    write_text("dc ");
    write_vector(*dvp);
    finish_line("");
}

void Pog_writer::operation_deletion(int var) {
    write_text("do %d", var);
    finish_line("");
}

void Pog_writer::constant(int cid, int val) {
    write_text("%d k %d", cid, val);
    finish_line("");
}
