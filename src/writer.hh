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


#pragma once

#include <stdio.h>
#include <cstdarg>
#include <stdbool.h>
#include <vector>
#include <unordered_set>
#include <set>

// Capability to write different file types

class Writer {
private:
    char *file_name;
    FILE *outfile;
    int line_count;
    bool do_comments;

public:

    Writer(const char *fname);
    Writer();
    void enable_comments();
    // Only produce comments when enabled
    void comment(const char *fmt, ...);
    void start_line();
    void add_int(int val);
    void add_text(const char *txt);
    // Write list/vector of literals with zero termination (but no EOL)
    void write_list(ilist vals);
    void write_vector(std::vector<int> &vec);

    // Write list of literals with zero termination and EOL as comment    
    void comment_list(const char *descr, ilist vals);

    // Write vector of literals with zero termination and EOL as comment
    void comment_container(const char *descr, std::vector<int> &vals);
    void comment_container(const char *descr, std::unordered_set<int> &vals);
    void comment_container(const char *descr, std::set<int> &vals);

    // Put diagnostic information in comment and stdout
    void diagnose(const char *fmt, ...);
    // Write list of literals with zero termination and EOL.
    void diagnose_list(const char *descr, ilist vals);
    // Write vector of literals with zero termination and EOL.
    void diagnose_container(const char *descr, std::vector<int> &vals);
    void diagnose_container(const char *descr, std::unordered_set<int> &vals);
    void diagnose_container(const char *descr, std::set<int> &vals);

    void finish_line(const char *txt);
    void finish_file();

    // Write text.  (Don't use EOL)
    void write_text(const char *fmt, ...);
};

class Cnf_writer : public Writer {

public:
    Cnf_writer();
    Cnf_writer(const char *fname);
    void write_header(int nvar, int nclause);

};

class Pog_writer : public Writer {

public:
    Pog_writer();
    Pog_writer(const char *fname);

    void declare_root(int root_literal);
    void start_assertion(int cid);
    void start_and(int cid, int var);
    void start_or(int cid, int var);
    void constant(int cid, int val);
    // Clause deletion.  Vector includes clause + hints
    void clause_deletion(std::vector<int> *dvp);
    void operation_deletion(int var);
};
