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

// Don't want any type to evaluate to 0
typedef enum { POG_NONE, POG_TRUE, POG_FALSE, POG_AND, POG_OR } pog_type_t;

#include <vector>
#include <stdio.h>
#include "clausal.hh"
#include "writer.hh"


// POG Nodes
class Pog_node {
private:
    // Basic representation
    pog_type_t type;
    // Extension variable for node
    int xvar;

    // Identify children by their representation as literals
    // Can be variable, other Pog node, or the negation of one of these
    // Organize so that literals representing nodes come at end
    // AND node can have any degree >= 2
    // OR  node must have degree 2,
    int degree;
    int *children;

    // Id of first clause in declaration
    int defining_cid;

    // Lemma support
    int indegree;
    Lemma_instance *lemma;

public:
    Pog_node();

    Pog_node(pog_type_t ntype);

    ~Pog_node();

    void set_type(pog_type_t t);
    pog_type_t get_type();
    void set_xvar(int var);
    int get_xvar();
    void set_defining_cid(int cid);
    int get_defining_cid();

    // Store name in local buffer.
    const char *name();

    // Set degree and import children
    void add_children(std::vector<int> *cvec);

    void show(FILE *outfile);

    // Access children
    int get_degree();
    int& operator[](int);

    // Lemma support
    void increment_indegree();
    // Does this node meet criteria for having a lemma?
    bool want_lemma();
    void add_lemma(Lemma_instance *lemma);
    Lemma_instance *get_lemma();
};

// POG
class Pog {
private:
    // Current CNF + proof generation support
    Cnf_reasoner *cnf;
    int max_input_var;
    std::vector<Pog_node *> nodes;
    // Root literal can refer to either an input variable or the last node
    int root_literal;

public:
    Pog();

    Pog(Cnf_reasoner *cset);

    // Readers
    bool read_pog(FILE *infile);
    bool read_ddnnf(FILE *infile);
    bool read_d4ddnnf(FILE *infile);

    int add_node(Pog_node *np);

    void set_root(int rlit);
    int get_root();

    // Does literal refer to an input variable or a node
    bool is_node(int lit);
    // Does literal refer to a node of specified type                                                                           
    bool is_node_type(int lit, pog_type_t type);

    // Index POG nodes by their extension variables
    Pog_node * get_node(int var);
    Pog_node * operator[](int);

    int node_count();

    void show(FILE *outfile);

    // At each position in POG, generate justification within context
    // Return ID of justifying clause
    int justify(int rlit, bool parent_or, bool use_lemma);

    bool delete_input_clause(int cid, int unit_cid, std::vector<int> &overcount_literals);

private:
    // Simplify POG by eliminating constants,
    //  eliminating common subnodes, etc.
    // Renumber Ids to be consecutive
    // Return false if something wrong with original POG
    bool optimize();
    // Add POG declarations to file
    bool concretize();
    // Helper routines
    void topo_order(int rlit, std::vector<int> &rtopo, int *markers);
    // Recursively descend Pog until find input literal
    int first_literal(int rlit);
    // Create/Apply lemma at node.  Return ID of justifying clause (0 if failed)
    int apply_lemma(Pog_node *rp, bool parent_or);
    // For generating counterexample when input deletion fails
    bool get_deletion_counterexample(int cid, std::vector<bool> &implies_clause, std::vector<int> &literals);
};
