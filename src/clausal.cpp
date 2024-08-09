/*========================================================================
  Copyright (c) 2022 Randal E. Bryant, Carnegie Mellon University
  
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

#include <iostream>
#include <ctype.h>
#include <algorithm>
#include <cstring>
#include <map>
#include "clausal.hh"
#include "report.h"
#include "counters.h"

#ifndef LOG
#define LOG 0
#endif

static int skip_line(FILE *infile) {
    int c;
    while ((c = getc(infile)) != EOF) {
	if (c == '\n')
	    return c;
    }
    return c;
}

// Skip over comment lines, spaces, newlines, etc., until find something interesting
// Return false if EOF encountered without finding anything
static bool find_token(FILE *infile) {
    int c;
    while ((c = getc(infile)) != EOF) {
	if (c == 'c') {
	    c = skip_line(infile);
	    ungetc(c, infile);
	} else if (!isspace(c)) {
	    ungetc(c, infile);
	    return true;
	}
	// Skip space
    }
    return false;
}

// Put literals in ascending order of the variables
static bool abs_less(int x, int y) {
    return abs(x) < abs(y);
}

Clause::Clause() { 
    contents = ilist_new(0);
    is_tautology = false;
    canonized = true;
    activating_literal = 0;
}

Clause::~Clause() { 
    ilist_free(contents);
}

Clause::Clause(int *array, size_t len) {
    is_tautology = false;
    canonized = false;
    contents = ilist_new(len);
    for (int i = 0; i < len; i++)
	add(array[i]);
    activating_literal = 0;
}

Clause::Clause(Clause *np) {
    is_tautology = false;
    canonized = np->canonized;
    contents = ilist_copy(np->contents);
    activating_literal = np->get_activating_literal();
}

Clause::Clause(FILE *infile, bool from_proof, bool *eof) {
    int rval;
    int lit;
    int c;
    is_tautology = false;
    contents = ilist_new(4);
    *eof = true;

    // Skip blank lines and comments
    while ((c = getc(infile)) != EOF) {
	if (c == 'c')
	    c = skip_line(infile);
	else if (from_proof && c == 'd')
	    c = skip_line(infile);
	else if (isspace(c))
	    continue;
	else {
	    ungetc(c, infile);
	    break;
	}
    }

    while ((rval = fscanf(infile, "%d", &lit)) == 1) {
	*eof = false;
	if (lit == 0)
	    break;
	else
	    add(lit);
    }
    if (!from_proof)
	canonize();
    activating_literal = 0;
}

void Clause::add(int val) {
    contents = ilist_push(contents, val);
    canonized = false;
}

size_t Clause::length() {
    if (is_tautology)
	return 0;
    return ilist_length(contents);
}

bool Clause::tautology() {
    return is_tautology;
}

int Clause::max_variable() {
    int mvar = 0;
    if (is_tautology)
	return 0;
    for (int i = 0; i < length(); i++) {
	int var = abs(contents[i]);
	mvar = std::max(var, mvar);
    }
    return mvar;
}

int * Clause::data() {
    return contents;
}


int& Clause::operator[](int i) {
    return contents[i];
}

int Clause::get_activating_literal() {
    return activating_literal;
}

void Clause::set_activating_literal(int alit) {
    activating_literal = alit;
}

bool Clause::satisfied(char *assignment) {
    bool found = is_tautology;
    for (int i = 0; !found && i < ilist_length(contents); i++) {
	int lit = contents[i];
	found = (lit < 0 && assignment[-lit-1] == 0) || (lit > 0 && assignment[lit-1] == 1);
    }
    return found;
}

bool Clause::contains(int lit) {
    for (int i = 0; i < ilist_length(contents); i++)
	if (contents[i] == lit)
	    return true;
    return false;
}

static char buf[10000];

void Clause::canonize() {
    if (canonized)
	return;
    
    std::sort(contents, contents + length(), abs_less);
    int last_lit = 0;
    size_t read_pos = 0;
    size_t write_pos = 0;
    is_tautology = false;
    while(read_pos < length()) {
	int lit = contents[read_pos++];
	if (abs(lit) == abs(last_lit)) {
	    if (lit != last_lit) {
		// Opposite literals encountered
		is_tautology = true;
		break;
	    }
	} else {
	    contents[write_pos++] = lit;
	}
	last_lit = lit;
    }
    if (is_tautology) {
	contents = ilist_resize(contents, 2);
	contents[0] = abs(last_lit);
	contents[1] = -abs(last_lit);
    } else
	contents = ilist_resize(contents, write_pos);
    canonized = true;
}

void Clause::show() {
    if (is_tautology) {
	std::cout << "c Tautology" << std::endl;
	std::cout << "1 -1 0" << std::endl;
	return;
    }
    for (int i = 0; i < length(); i++)
	std::cout << contents[i] << ' ';
    std::cout << '0' << std::endl;
}

void Clause::show(std::ofstream &outstream) {
    if (is_tautology) {
	outstream << "c Tautology" << std::endl;
	outstream << "1 -1 0" << std::endl;
	return;
    }
    for (int i = 0; i < length(); i++)
	outstream << contents[i] << ' ';
    outstream << '0' << std::endl;
}

void Clause::show(FILE *outfile) {
    if (is_tautology) {
	fprintf(outfile, "c Tautology\n");
	fprintf(outfile, "1 -1 0\n");
	return;
    }
    for (int i = 0; i < length(); i++)
	fprintf(outfile, "%d ", contents[i]);
    fprintf(outfile, "0\n");
}

void Clause::show_reduced(FILE *outfile, int ulit) {
    // See if clause becomes tautology
    bool tautology = is_tautology;
    for (int i = 0; !tautology && i < length(); i++)
	if (contents[i] == ulit)
	    tautology = true;
    if (tautology)
	fprintf(outfile, "%d %d ", ulit, -ulit);
    else
	for (int i = 0; i < length(); i++) {
	    int lit = contents[i];
	    if (lit != -ulit)
		fprintf(outfile, "%d ", lit);
	}
    fprintf(outfile, "0\n");	
}

void Clause::write(Writer *writer) {
    if (is_tautology) {
	int tclause[2 + ILIST_OVHD];
	ilist ils = ilist_make(tclause, 2);
	ilist_fill2(ils, 1, -1);
	writer->write_list(ils);
	return;
    }
    writer->write_list(contents);
}

ilist Clause::simplify(std::unordered_set<int> &unit_literals) {
    ilist lits = ilist_new(0);
    bool satisfied = false;
    for (int i = 0; i < length(); i++) {
	int lit = contents[i];
	if (unit_literals.find(lit) != unit_literals.end()) {
	    satisfied = true;
	    break;
	} else if (unit_literals.find(-lit) == unit_literals.end())
	    lits = ilist_push(lits, lit);
    }
    if (satisfied)
	return NULL;
    return lits;
}



// Support for computing hash function over clause
// Represent by signature over modular field
static const unsigned hash_modulus = 2147483647U;
static char hash_state[256];

static std::vector<unsigned> var_hash;

#define CHUNK_SIZE 1024

static unsigned next_hash_int(unsigned sofar, int val) {
    if (var_hash.size() == 0) {
	// Initialization
	initstate(1, hash_state, 256);
    }
    unsigned var = IABS(val);
    if (var >= var_hash.size()) {
	// Add more random values
	size_t osize = var_hash.size();
	size_t nsize = osize + (1 + (var - osize)/CHUNK_SIZE) * CHUNK_SIZE;
	var_hash.resize(nsize);
	char *ostate = setstate(hash_state);
	for (unsigned i = osize; i < nsize; i++)
	    var_hash[i] = random() % hash_modulus;
	setstate(ostate);
    }
    unsigned vval = var_hash[var];
    unsigned long  lval = val < 0 ? 1 + hash_modulus - vval : vval;
    return (lval * sofar) % hash_modulus;
}
    
unsigned Clause::hash() {
    canonize();
    unsigned val = 1;
    for (int i = 0; i < length(); i++)
	val = next_hash_int(val, contents[i]);
    return val;
}

bool Clause::is_equal(Clause *op) {
    canonize();
    op->canonize();
    if (length() != op->length())
	return false;
    if (tautology() != op->tautology())
	return false;
    for (int i = 0; i < length(); i++)
	if (contents[i] != (*op)[i])
	    return false;
    return true;
}

Cnf::Cnf() { read_failed = false; proof_failed = false; max_input_var = 0; }

Cnf::Cnf(FILE *infile) { 
    int expectedMax = 0;
    int expectedCount = 0;
    read_failed = false;
    proof_failed = false;
    max_input_var = 0;
    bool got_header = false;
    bool no_header = false;
    int c;
    // Look for CNF header
    while ((c = getc(infile)) != EOF) {
	if (isspace(c)) 
	    continue;
	if (c == 'c' || c == 'd')
	    c = skip_line(infile);
	if (c == 's') {
	    // Failed proof
	    proof_failed = true;
	    return;
	}
	if (c == EOF) {
	    err(false, "Not valid CNF file.  No header line found\n");
	    read_failed = true;
	    return;
	}
	if (c == 'p') {
	    char field[20];
	    if (fscanf(infile, "%s", field) != 1) {
		err(false, "Not valid CNF file.  Invalid header line\n");
		read_failed = true;
		return;
	    }
	    if (strcmp(field, "cnf") != 0) {
		err(false, "Not valid CNF file.  Header line shows type is '%s'\n", field);
		read_failed = true;
		return;
	    }
	    if (fscanf(infile, "%d %d", &expectedMax, &expectedCount) != 2) {
		err(false, "Invalid CNF header\n");
		read_failed = true;
		return;
	    } 
	    c = skip_line(infile);
	    got_header = true;
	    break;
	}
	if (c == EOF) {
	    err(false, "Invalid CNF.  EOF encountered before reading any clauses\n");
	    read_failed = true;
	    return;
	}
	if (isdigit(c) || c == '-') {
	    no_header = true;
	    ungetc(c, infile);
	    break;
	}
    }
    if (!got_header && !no_header) {
	err(false, "Not valid CNF.  No header line found\n");
	read_failed = true;
	return;
    }
    while (1) {
	bool eof = false;
	Clause *clp = new Clause(infile, !got_header, &eof);
	if (eof || read_failed)
	    break;
	add(clp);

    }
    if (!no_header && max_input_var > expectedMax) {
	err(false, "Invalid CNF.  Encountered variable %d. Expected max = %d\n",  max_input_var, expectedMax);
	read_failed = true;
	return;
    }
    if (!no_header && clause_count() != expectedCount) {
	err(false, "Read %d clauses.  Expected %d\n", clause_count(), expectedCount);
	read_failed = true;
	return;
    }
    if (!no_header) {
	incr_count_by(COUNT_CLAUSE, clause_count());
	incr_count_by(COUNT_VAR, max_input_var);
    }
}

// Delete the clauses
Cnf::~Cnf() { 
#if 0
    for (Clause *np : clauses) {
	delete np;
    }
#endif
}

bool Cnf::failed() {
    return read_failed;
}

void Cnf::add(Clause *clp) {
    clauses.push_back(clp);
    int mvar = clp->max_variable();
    max_input_var = std::max(max_input_var, mvar);
}

Clause * Cnf::get_input_clause(int cid) {
    int input_count = clauses.size();
    if (cid <= input_count)
	return clauses[cid-1];
    else {
	err(true, "Fatal.  Trying to access clause #%d.  Have %d input clauses\n", cid, input_count);
	exit(1);
    }
}

unsigned Cnf::hash() {
    unsigned sig = 1;
    for (Clause *cp : clauses) {
	sig = next_hash_int(sig, cp->hash());
    }
    return sig;
}

Clause * Cnf::operator[](int cid) {
    return get_input_clause(cid);
}

void Cnf::show() {
    std::cout << "p cnf " << max_input_var << " " << clause_count() << std::endl;
    for (std::vector<Clause *>::iterator clp = clauses.begin(); clp != clauses.end(); clp++) {
	(*clp)->show();
    }
}

void Cnf::show(std::ofstream &outstream) {
    outstream << "p cnf " << max_input_var << " " << clause_count() << std::endl;
    for (std::vector<Clause *>::iterator clp = clauses.begin(); clp != clauses.end(); clp++) {
	(*clp)->show(outstream);
    }
}

void Cnf::show(FILE *outfile) {
    fprintf(outfile, "p cnf %d %d\n", max_input_var, (int) clause_count());
    for (std::vector<Clause *>::iterator clp = clauses.begin(); clp != clauses.end(); clp++) {
	(*clp)->show(outfile);
    }
}

size_t Cnf::clause_count() {
    return clauses.size();
}

int Cnf::max_variable() {
    return max_input_var;
}

int Cnf::satisfied(char *assignment) {
    for (int cid = 1; cid <= clauses.size(); cid++) {
	Clause *cp = clauses[cid-1];
	if (!cp->satisfied(assignment))
	    return cid;
    }
    return 0;
}

// Support for generating reduced CNF, running through SAT solver, and mapping proof steps back to original
Cnf_reduced::Cnf_reduced() : Cnf() {
    emitted_proof_clauses = 0;
    unsatisfiable = false;
    delete_files = true;
}

Cnf_reduced::~Cnf_reduced() {
    for (Clause *np : proof_clauses) {
	if (np)
	    delete np;
    }
    // Could delete the temporary files here.
    for (const char *fname : file_names) {
	if (delete_files)
	    remove(fname);
	free((void *) fname);
    }
}

const char *Cnf_reduced::get_file_name() {
    if (file_names.size() >= 1)
	return file_names[0];
    else
	return "Unknown";
}

void Cnf_reduced::add_clause(Clause *np, std::unordered_set<int> &unit_literals, int cid) {
    ilist slits = np->simplify(unit_literals);
    if (slits != NULL) {
	Clause *snp = new Clause(slits, ilist_length(slits));
	add(snp);
	inverse_cid[clause_count()] = cid;
	if (snp->length() == 0)
	    unsatisfiable = true;
    }
}

// Special version of show that includes comments
void Cnf_reduced::show(FILE *outfile) {
    fprintf(outfile, "p cnf %d %d\n", max_variable(), (int) clause_count());
#if DEBUG
    int cid = 0;
#endif
    for (std::vector<Clause *>::iterator clp = clauses.begin(); clp != clauses.end(); clp++) {
#if DEBUG
	cid++;
	fprintf(outfile, "c local clause %d -> global clause %d\n", cid, inverse_cid.find(cid)->second);
#endif
	(*clp)->show(outfile);
    }
}


bool Cnf_reduced::run_solver() {
    incr_count(COUNT_SAT_CALL);
    static int vnum = 1000000;
    char tname[100];
    char cmd[150];
    
    if (unsatisfiable) {
	err(false, "Reduced CNF contains empty clause\n");
	return true;
    }

    snprintf(tname, 100, "reduction-%d.cnf", ++vnum);
    
    FILE *cout = fopen(tname, "w");
    if (cout == NULL) {
	err(false, "Couldn't open temporary CNF file %s\n", tname);
	return false;
    }
    const char *fname = archive_string(tname);
    file_names.push_back(fname);
    show(cout);
    fclose(cout);
    report(3, "Wrote file with %d clauses to %s\n", clause_count(), fname);
    
    double start = tod();
    snprintf(cmd, 150, "cadical --unsat -q --no-binary %s -", fname);
    FILE *sfile = popen(cmd, "r");
    if (sfile == NULL) {
	err(true, "Couldn't execute command '%s'\n", cmd);
    }
    Cnf pclauses(sfile);
    pclose(sfile);
    incr_timer(TIME_SAT, tod()-start);

    report(3, "Read %d proof clauses\n", pclauses.clause_count());
    if (verblevel >= 5)
	pclauses.show();

    if (pclauses.proof_failed) {
	err(false, "Execution of command '%s' shows formula satisfiable\n", cmd);
	return false;
    }

    if (pclauses.clause_count() == 0) {
	err(true, "Execution of command '%s' yielded no proof clauses\n", cmd);
	return false;
    }

    Clause *lnp = pclauses[pclauses.clause_count()];
    if (lnp == NULL) {
	err(false, "Invalid final clause after executing command '%s'\n", cmd);
	return false;
    }
    if (lnp->length() != 0) {
	err(false, "Execution of command '%s' did not generate empty clause\n", cmd);	
	return false;
    }

    for (int cid = 1; cid <= pclauses.clause_count(); cid++) {
	Clause *pnp = pclauses[cid];
	proof_clauses.push_back(pnp);
	if (pnp->length() == 0)
	    break;
    }
    double micro = (tod() - start) * 1e6;
#if LOG
    log_data("s,%u,%d,%d,%.0f\n", hash(), clause_count(), pclauses.clause_count(), micro);
#endif
    report(3, "File %s.  %d input clauses --> %d proof clauses (%.0f us)\n", fname, clause_count(), proof_clauses.size(), micro);
    incr_histo(HISTO_PROBLEM, clause_count());
    incr_histo(HISTO_PROOF, proof_clauses.size());

    return true;
}

bool Cnf_reduced::run_hinting_solver() {
    incr_count(COUNT_SAT_CALL);
    static int vnum = 1000000;
    char tcnfname[100];
    char tlratname[100];
    char cmd[350];

    if (unsatisfiable) {
	err(false, "Reduced CNF contains empty clause\n");
	return true;
    }

    snprintf(tcnfname, 100, "reduction-%d.cnf", ++vnum);
    FILE *cout = fopen(tcnfname, "w");
    if (cout == NULL) {
	err(false, "Couldn't open temporary CNF file %s\n", tcnfname);
	return false;
    }
    const char *cnfname = archive_string(tcnfname);
    file_names.push_back(cnfname);
    show(cout);
    fclose(cout);
    report(3, "Wrote file with %d clauses to %s\n", clause_count(), cnfname);
    
    snprintf(tlratname, 100, "reduction-%d.lrat", vnum);
    const char *lratname = archive_string(tlratname);
    file_names.push_back(lratname);

    double start = tod();
    snprintf(cmd, 350, "cadical --no-binary --unsat -q %s - | drat-trim %s -L %s > /dev/null", cnfname, cnfname, lratname);
    //snprintf(cmd, 350, "cadical --unsat -q %s - | drat-trim %s -L %s > /dev/null", cnfname, cnfname, lratname);
    int rc = system(cmd);
    incr_timer(TIME_SAT, tod()-start);
    if (rc != 0)
	err(false, "Executing command '%s' yielded return code %d\n", cmd, rc);
    FILE *lfile = fopen(lratname, "r");
    if (!lfile) {
	err(false, "Couldn't open generated LRAT file\n", lratname);
	return false;
    }
    if (!load_hinted_proof(lfile)) {
	err(false, "Failed to read generated LRAT file\n", lratname);
	return false;
    }
    fclose(lfile);
    if (proof_clauses.size() == 0) {
	err(false, "Execution of command '%s' yielded no proof clauses\n", cmd);
	return false;
    }
    report(3, "Drat-trim.  %s %d problem clauses.  %d proof clauses\n", cnfname, clause_count(), proof_clauses.size()); 
    Clause *lnp = proof_clauses.back();
    if (lnp->length() != 0) {
	err(false, "Execution of command '%s' did not generate empty clause\n", cmd);	
	return false;
    }
    double micro = (tod() - start) * 1e6;
#if LOG
    log_data("t,%u,%d,%d,%.0f\n", hash(), clause_count(), proof_clauses.size(), micro);
#endif
    report(3, "File %s.  %d input clauses --> %d proof clauses (%.0f us)\n", cnfname, clause_count(), proof_clauses.size(), micro);
    incr_histo(HISTO_PROBLEM, clause_count());
    incr_histo(HISTO_PROOF, proof_clauses.size());
    return true;
}


// Read proof clauses + hints in LRAT format.
// Ignore deletions
// Return true if successful
bool Cnf_reduced::load_hinted_proof(FILE *infile) {
    int nclause = clause_count();
    std::unordered_map<int,int> lrat2local;
    int next_id = nclause + 1;
    while (find_token(infile)) {
	int sid = 0;
	if (fscanf(infile, "%d", &sid) != 1) {
	    err(false, "Couldn't read step Id in LRAT file.  Should be at step #%d\n", next_id);
	    return false;
	}
	if (!find_token(infile)) {
	    err(false, "EOF found while trying to parse proof step #%d\n", next_id);
	}
	int c = getc(infile);
	if (c == EOF) {
	    err(false, "EOF found while trying to parse proof step #%d\n", sid);
	    return false;
	}
	if (c == 'd') {
	    c = skip_line(infile);
	    if (c == EOF) {
		err(false, "EOF found while trying to parse proof step #%d\n", sid);
		return false;
	    }
	    ungetc(c, infile);
	    continue;
	} else
	    ungetc(c, infile);
	// Here's the good stuff
	bool eof;
	Clause *np = new Clause(infile, true, &eof);
	if (np == NULL || eof) {
	    err(false, "Error encountered while trying to read literals from proof step #%d\n", sid);
	    return false;
	}
	Clause *hp = new Clause(infile, true, &eof);
	if (hp == NULL || eof) {
	    err(false, "Error encountered while trying to read hints from proof step #%d\n", sid);
	    return false;
	}
	lrat2local[sid] = next_id;
	// Fix up hints
	for (int i = 0; i < hp->length(); i++) {
	    int hint = (*hp)[i];
	    int nhint = (hint <= nclause) ? hint : lrat2local.find(hint)->second;
	    (*hp)[i] = nhint;
	}
	proof_clauses.push_back(np);
	proof_hints.push_back(hp);
	next_id++;
    }
    return true;
}

// Retrieve hints for next clause in proof.
// Remap hint clause Ids to ones that match those in the larger proof
// start_id should be Id for first clause in proof sequence
Clause * Cnf_reduced::get_proof_hint(int start_id) {
    if (emitted_proof_clauses >= proof_hints.size())
	return NULL;
    Clause *hp = proof_hints[emitted_proof_clauses];
    Clause *nhp = new Clause();
    int ccount = clause_count();
    for (int i = 0; i < hp->length(); i++) {
	int hint = (*hp)[i];
	int nhint = hint <= ccount ? inverse_cid[hint] : start_id + hint - ccount - 1;
	nhp->add(nhint);
    }
    delete hp;
    return nhp;
}

// Retrieve next clause in proof.  Convert it to one usable by parent solver
Clause * Cnf_reduced::get_proof_clause(std::vector<int> *context) {
    if (emitted_proof_clauses >= proof_clauses.size())
	return NULL;
    Clause *np = proof_clauses[emitted_proof_clauses];
    Clause *nnp = new Clause(np);
    for (int lit : *context) 
	nnp->add(-lit);
    delete np;
    proof_clauses[emitted_proof_clauses++] = NULL;
    return nnp;
}



// Proof related
Cnf_reasoner::Cnf_reasoner(FILE *infile) : Cnf(infile) { 
    pwriter = NULL;
    asserting = false;
    unsatisfiable = false;
    multi_literal = true;
    use_lemmas = true;
    delete_files = true;
    drat_threshold = 1000;
    clause_limit = INT_MAX;
    bcp_limit = 1;
    xvar_count = max_variable();
}

Clause * Cnf_reasoner::get_clause(int cid) {
    int input_count = clause_count();
    int proof_count = proof_clauses.size();
    if (cid <= input_count)
	return get_input_clause(cid);
    else {
	Clause *np = get_aux_clause(cid);
	if (np != NULL)
	    return np;
	else if (cid <= input_count + proof_count)
	    return proof_clauses[cid - input_count - 1];
	else {
	    err(true, "Fatal.  Trying to access clause #%d.  Have %d input and %d proof clauses\n", cid, input_count, proof_count);
	    exit(1);
	}
    }
}


Clause * Cnf_reasoner::operator[](int cid) {
    return get_clause(cid);
}

bool Cnf_reasoner::is_unsatisfiable() {
    return unsatisfiable;
}

void Cnf_reasoner::activate_clause(int cid) {
    curr_active_clauses->insert(cid);
}

void Cnf_reasoner::deactivate_clause(int cid) {
    curr_active_clauses->erase(cid);
}

int Cnf_reasoner::add_proof_clause(Clause *clp) {
    int pcid = clause_count() + proof_clauses.size();
    if (pcid == clause_limit) {
	err(true, "Adding clause %ld exceeds limit\n", (long) pcid + 1);
    }
    int cid = pcid + 1;
    proof_clauses.push_back(clp);
    if (clp->length() == 0)
	unsatisfiable = true;
    else if (clp->length() == 1) {
	int lit = (*clp)[0];
	unit_literals.insert(lit);
	justifying_ids[lit] = cid;
    }
    return cid;
}

int Cnf_reasoner::start_assertion(Clause *clp) {
    int cid = add_proof_clause(clp);
    pwriter->start_assertion(cid);
    clp->write(pwriter);
    std::vector<int> *dvp = new std::vector<int>();
    dvp->push_back(cid);
    asserting = true;   
    deletion_stack.push_back(dvp);
    return cid;
}

void Cnf_reasoner::add_hint(int hid) {
    pwriter->add_int(hid);
    if (asserting) {
	std::vector<int> *dvp = deletion_stack.back();
	dvp->push_back(hid);
    }
}

void Cnf_reasoner::add_hints(Clause *hp) {
    for (int i = 0; i < hp->length(); i++) 
	add_hint((*hp)[i]);
}


void Cnf_reasoner::finish_command(bool add_zero) {
    if (add_zero)
	pwriter->finish_line("0");
    else
	pwriter->finish_line("");
    asserting = false;
}

void Cnf_reasoner::document_input(int cid) {
    ilist show = ilist_new(0);
    Clause *cp = get_clause(cid);
    show = ilist_push(show, cid);
    for (int i = 0; i < cp->length(); i++)
	show = ilist_push(show, (*cp)[i]);
    show = ilist_push(show, 0);
    pwriter->comment_list("", show);
    ilist_free(show);
}

int Cnf_reasoner::start_and(int var, ilist args) {
    pwriter->comment("Operation N%d_AND", var);
    Clause *clp = new Clause();
    clp->add(var);
    for (int i = 0; i < ilist_length(args); i++) 
	clp->add(-args[i]);
    int cid = add_proof_clause(clp);
    long ncid = (long) cid + ilist_length(args);
    if (ncid > clause_limit)
	err(true, "Adding operation with %d arguments starting with clause %d exceeds limit\n", ilist_length(args), cid);
    for (int i = 0; i < ilist_length(args); i++) {
	Clause *aclp = new Clause();
	aclp->add(-var);
	aclp->add(args[i]);
	add_proof_clause(aclp);
    }
    pwriter->start_and(cid, var);
    pwriter->write_list(args);
    incr_count_by(COUNT_DEFINING_CLAUSE, ilist_length(args)+1);
    return cid;
}

void Cnf_reasoner::document_and(int cid, int var, ilist args) {
    if (verblevel < 2) 
	return;
    pwriter->comment("Implicit declarations");
    int len = ilist_length(args);
    ilist show = ilist_new(len+2);
    ilist_resize(show, len+2);
    show[0] = cid;
    show[1] = var;
    for (int i = 0; i < len; i++)
	show[i+2] = -args[i];
    pwriter->comment_list("", show);
    show = ilist_resize(show, 3);
    for (int i = 0; i < ilist_length(args); i++) {
	show[0] = cid+i+1;
	show[1] = -var;
	show[2] = args[i];
	pwriter->comment_list("", show);
    }
    ilist_free(show);
}


int Cnf_reasoner::start_or(int var, ilist args) {
    pwriter->comment("Operation N%d_OR", var);
    int arg1 = args[0];
    int arg2 = args[1];
    Clause *clp = new Clause();
    clp->add(-var); clp->add(arg1); clp->add(arg2);
    int cid = add_proof_clause(clp);
    if (cid + ilist_length(args) > clause_limit)
	err(true, "Adding operation starting with clause %d exceeds limit\n", cid);
    Clause *aclp1 = new Clause();
    aclp1->add(var); aclp1->add(-arg1);
    add_proof_clause(aclp1);
    Clause *aclp2 = new Clause();
    aclp2->add(var); aclp2->add(-arg2);
    add_proof_clause(aclp2);
    pwriter->start_or(cid, var);
    pwriter->add_int(arg1); pwriter->add_int(arg2);
    incr_count_by(COUNT_DEFINING_CLAUSE, ilist_length(args)+1);
    return cid;
}

void Cnf_reasoner::document_or(int cid, int var, ilist args) {
    if (verblevel < 2)
	return;
    pwriter->comment("Implicit declarations");
    int len = ilist_length(args);
    ilist show = ilist_new(len+2);
    ilist_resize(show, len+2);
    show[0] = cid;
    show[1] = -var;
    for (int i = 0; i < len; i++)
	show[i+2] = args[i];
    pwriter->comment_list("", show);
    show = ilist_resize(show, 3);
    for (int i = 0; i < ilist_length(args); i++) {
	show[0] = cid+i+1;
	show[1] = var;
	show[2] = -args[i];
	pwriter->comment_list("", show);
    }
    ilist_free(show);
}

int Cnf_reasoner::assert_literal(int lit) {
    pwriter->comment("Assert %d as unit literal without proof", lit);
    Clause *clp = new Clause();
    clp->add(lit);
    int cid = start_assertion(clp);
    finish_command(true);
    incr_count(COUNT_LITERAL_JUSTIFICATION_CLAUSE);
    return cid;
}


// Got a new unit literal.
void Cnf_reasoner::new_unit(int lit, int cid, bool input) {
    if (input) {
	unit_literals.insert(lit);
	justifying_ids[lit] = cid;
	report(3, "Unit literal %d justified by input clause #%d\n", lit, cid);
	return;
    }
    Clause *cp = get_clause(cid);
    int clen = cp->length();
    // Optimization: Don't generate new clause if unit implied by context literals
    bool need_new = false;
    for (int idx = 0; idx < clen; idx++) {
	int clit = (*cp)[idx];
	if (justifying_ids.find(-clit) != justifying_ids.end())
	    need_new = true;
    }
    if (!need_new) {
	push_derived_literal(lit, cid);
	report(3, "Unit literal %d already justified by clause #%d\n", lit, cid);
	return;
    }
    Clause *clp = new Clause();
    clp->add(lit);
    for (int alit : assigned_literals)
	clp->add(-alit);
#if DEBUG
    pwriter->comment("Justified literal %d", lit);
#endif
    int ncid = start_assertion(clp);
    if (clp->length() == 1) {
	unit_literals.insert(lit);
    } else {
	push_derived_literal(lit, ncid);
    }
    // Print hints
    for (int idx = 0; idx < clen; idx++) {
	int clit = (*cp)[idx];
	auto fid = justifying_ids.find(-clit);
	if (fid != justifying_ids.end()) {
	    add_hint(fid->second);
	}
    }
    add_hint(cid);
    finish_command(true);
    incr_count(COUNT_LITERAL_JUSTIFICATION_CLAUSE);
    report(3, "Unit literal %d justified by proof clause #%d\n", lit, ncid);
}

int Cnf_reasoner::quick_validate_literal(int lit, int cid1, int cid2) {
    Clause *clp = new Clause();
    clp->add(lit);
    for (int alit : assigned_literals)
	clp->add(-alit);
    int ncid = start_assertion(clp);
    if (clp->length() == 1) {
	unit_literals.insert(lit);
    } else {
	push_derived_literal(lit, ncid);
    }
    add_hint(cid1);
    add_hint(cid2);
    finish_command(true);
    incr_count(COUNT_LITERAL_JUSTIFICATION_CLAUSE);
    return ncid;
}

int Cnf_reasoner::found_conflict(int cid) {
    Clause *clp = NULL;
    int ncid = 0;
    // Print hints
    Clause *cp = get_clause(cid);
    int clen = cp->length();
    bool found_hint = false;
    for (int idx = 0; idx < clen; idx++) {
	int clit = (*cp)[idx];
	auto fid = justifying_ids.find(-clit);
	if (fid != justifying_ids.end()) {
	    if (!found_hint) {
		found_hint = true;
		clp = new Clause();
		for (int alit : assigned_literals)
		    clp->add(-alit);
#if DEBUG
		pwriter->comment("Conflict clause");
#endif
		ncid = start_assertion(clp);
	    }
	    add_hint(fid->second);
	}
    }
    if (!found_hint)
	return cid;
    if (clp->length() == 1) {
	unit_literals.insert((*clp)[0]);
    }
    add_hint(cid);
    finish_command(true);
    incr_count(COUNT_LITERAL_JUSTIFICATION_CLAUSE);
    return ncid;
}

void Cnf_reasoner::reset_xvar() {
    xvar_count = max_variable();
}

int Cnf_reasoner::new_xvar() {
    return ++xvar_count;
}

// Enable POG generation
bool Cnf_reasoner::enable_pog(Pog_writer *pw) {
    pwriter = pw;
    // Set up active clauses
    curr_active_clauses = new std::set<int>;
    next_active_clauses = new std::set<int>;

    // Scan all clauses.  Find unit clauses.  Register non-tautologies
    int cid = 0;
    for (std::vector<Clause *>::iterator clp = clauses.begin(); clp != clauses.end(); clp++) {
	cid++;
	Clause *cp = *clp;
	if (cp->tautology())
	    continue;
	else if (cp->length() == 1) {
	    new_unit((*cp)[0], cid, true);
	    continue;
	}
	else
	    activate_clause(cid);
    }
    int ncid = bcp(false);
    if (ncid > 0) {
	pwriter->comment("Read failed.  Formula unsatisfiable (justifying ID = %d)", ncid);
	return false;
    };
    return true;
}

// Perform Boolean constraint propagation
// Return ID of any generated conflict clause (or 0)
// Each pass uses clauses from current active clauses and adds to next active clauses
// And then swaps the two sets
int Cnf_reasoner::bcp(bool bounded) {
    bool converged = false;
    bool conflict = false;
    int ncid = 0;
    int pcount = 0;
    while (!converged && !conflict) {
	if (bounded && pcount >= bcp_limit && curr_active_clauses->size() >= drat_threshold) 
	    break;
	pcount++;
	converged = true;
	if (verblevel >= 3) {
	    report(3, "BCP Pass %d.  Active clauses:", pcount);
	    for (int cid : *curr_active_clauses) {
		report(3, " %d", cid);
	    }
	    report(3, "\n");
	}
	for (int cid : *curr_active_clauses) {
	    if (conflict) {
		// Skip through clauses after conflict
		next_active_clauses->insert(cid);
		continue;
	    }
	    int ulit = 0;
	    bool multi_active = false;
	    conflict = true;
	    Clause *cp  = get_clause(cid);
	    if (verblevel >= 3) {
		report(3, "  Checking clause #%d: ", cid);
		cp->show(stdout);
		report(3, "  Unit literals:");
		for (int ulit : unit_literals) {
		    report(3, " %d", ulit);
		}
		report(3, "\n");
	    }
	    for (int idx = 0; idx < cp->length(); idx++) {
		int clit = (*cp)[idx];
		if (unit_literals.find(clit) != unit_literals.end()) {
		    report(3, "    Clause satisfied by unit %d\n", clit);
		    // Clause satisfied.
		    ulit = 0;
		    conflict = false;
		    multi_active = false;
		    push_clause(cid, false);
		    break;
		} else if (multi_active) {
		    continue;
		} else if (unit_literals.find(-clit) != unit_literals.end()) {
		    report(3, "    Literal %d falsified\n", clit);
		    continue;
		} else if (ulit == 0) {
		    report(3, "    Potential unit %d\n", clit);
		    // Potential unit
		    ulit = clit;
		    conflict = false;
		} else {
		    report(3, "    Additional unassigned literal %d\n", clit);
		    // Multiple unassigned literals
		    ulit = 0;
		    multi_active = true;
		}
	    }
	    if (conflict) {
		report(3, "    Conflict\n");
		ncid = found_conflict(cid);
		push_clause(cid, false);
	    } else if (ulit != 0) {
		report(3, "    Unit %d\n", ulit);
		new_unit(ulit, cid, false);
		converged = false;
		push_clause(cid, false);
	    } else if (multi_active) {
		report(3, "    Still active\n");
		next_active_clauses->insert(cid);
	    }
	}
	// Swap active clause sets
	std::set<int> *tmp =  curr_active_clauses;
	curr_active_clauses = next_active_clauses;
	next_active_clauses = tmp;
	next_active_clauses->clear();
    }
    return ncid;
}

// Generate set of hints for clause based on RUP validation
// Add clause as assertion
// Return ID of proof clause (or 0)
int Cnf_reasoner::rup_validate(Clause *cltp) {
    // List of clause Ids that have been used in unit propagation
    std::vector<int> prop_clauses;
    // Initialize with all known units:
    for (int ulit : unit_literals) {
	auto fid = justifying_ids.find(ulit);
	if (fid != justifying_ids.end())
	    prop_clauses.push_back(fid->second);
    }
    if (verblevel >= 3) {
	report(3, "\nStarting RUP deriviation of clause ");
	cltp->show(stdout);
    }
    new_context();
    // Negate literals in target clause
    for (int idx = 0; idx < cltp->length(); idx++) {
	int tlit = (*cltp)[idx];
	if (unit_literals.find(-tlit) == unit_literals.end()) {
	    push_assigned_literal(-tlit);
	}
    }
    // Unit propagation
    bool converged = false;
    bool conflict = false;
    while (!converged && !conflict) {
	converged = true;
	if (verblevel >= 3) {
	    report(3, "BCP Pass.  Active clauses:");
	    for (int cid : *curr_active_clauses) {
		report(3, " %d", cid);
	    }
	    report(3, "\n");
	}
	for (int cid : *curr_active_clauses) {
	    if (conflict) {
		// After encountering conflict, skip over remaining clauses
		next_active_clauses->insert(cid);
		continue;
	    }
	    int ulit = 0;
	    bool multi_active = false;
	    conflict = true;
	    Clause *cp  = get_clause(cid);
	    if (verblevel >= 3) {
		report(3, "  Checking clause #%d: ", cid);
		cp->show(stdout);
		report(3, "  Unit literals:");
		for (int ulit : unit_literals) {
		    report(3, " %d", ulit);
		}
		report(3, "\n");
	    }
	    for (int idx = 0; idx < cp->length(); idx++) {
		int clit = (*cp)[idx];
		if (unit_literals.find(clit) != unit_literals.end()) {
		    report(3, "    Clause satisfied by unit %d\n", clit);
		    // Clause satisfied.
		    ulit = 0;
		    conflict = false;
		    multi_active = false;
		    push_clause(cid, true);
		    break;
		} else if (multi_active) {
		    continue;
		} else if (unit_literals.find(-clit) != unit_literals.end()) {
		    report(3, "    Literal %d falsified\n", clit);
		    continue;
		} else if (ulit == 0) {
		    report(3, "    Potential unit %d\n", clit);
		    // Potential unit
		    ulit = clit;
		    conflict = false;
		} else {
		    report(3, "    Additional unassigned literal %d\n", clit);
		    // Multiple unassigned literals
		    ulit = 0;
		    multi_active = true;
		}
	    }
	    if (conflict) {
		report(3, "    Conflict\n");
		prop_clauses.push_back(cid);
		push_clause(cid, true);
	    } else if (ulit != 0) {
		report(3, "    Unit %d\n", ulit);
		prop_clauses.push_back(cid);
		push_derived_literal(ulit, cid);
		push_clause(cid, true);
		converged = false;
	    } else if (multi_active) {
		report(3, "    Still active\n");
		next_active_clauses->insert(cid);
	    }
	}
	// Swap active clause sets
	std::set<int> *tmp =  curr_active_clauses;
	curr_active_clauses = next_active_clauses;
	next_active_clauses = tmp;
	next_active_clauses->clear();
    }
    int ncid = 0;
    if (conflict) {
	// Construct hints in reverse order
	report(3, "Conflict found.  Constructing hints\n");
	std::vector<int> hints;
	std::unordered_set<int> used_set;
	std::reverse(prop_clauses.begin(), prop_clauses.end());
	used_set.insert(prop_clauses.front());
	for (int hid : prop_clauses) {
	    if (used_set.find(hid) != used_set.end()) {
		hints.push_back(hid);
		report(3, "  Clause #%d added to hints\n", hid);
		Clause *clp = get_clause(hid);
		for (int idx = 0; idx < clp->length(); idx++) {
		    int lit = (*clp)[idx];
		    auto fid = justifying_ids.find(-lit);
		    if (fid != justifying_ids.end()) {
			int jid = fid->second;
			used_set.insert(jid);
			report(3, "    Literal %d justified by clause #%d\n", -lit, jid);
		    } else {
			report(3, "    No justifying clause found for literal %d\n", -lit);
		    }
		}
	    } else
		report(3, "  Clause #%d not needed as hint\n", hid);
	}
	// Put hints in proper order
	std::reverse(hints.begin(), hints.end());
	ncid = start_assertion(cltp);
	for (int hid : hints)
	    add_hint(hid);
	finish_command(true);
	incr_count(COUNT_LITERAL_JUSTIFICATION_CLAUSE);
	activate_clause(ncid);
    }
    // Undo assignments
    pop_context();
    return ncid;
}


// Used to mark new layer in context stacks
#define CONTEXT_MARKER 0

void Cnf_reasoner::new_context() {
    context_literal_stack.push_back(CONTEXT_MARKER);
    context_cleared_literal_stack.push_back(CONTEXT_MARKER);
    context_clause_stack.push_back(CONTEXT_MARKER);
    report(4, "New context\n");
}

std::vector<int> *Cnf_reasoner::get_assigned_literals() {
    return &assigned_literals;
}

void Cnf_reasoner::push_assigned_literal(int lit) {
    //  For some strange reason, this warning gets triggered when it shouldn't.
    if (unit_literals.find(lit) != unit_literals.end()) {
	err(false, "Attempt to assert literal %d.  But, it is already unit\n", lit);
#if DEBUG
	pwriter->comment("Attempt to assert literal %d.  But, it is already unit", lit);
	pwriter->comment_container("  Current unit literals", unit_literals);
#endif 
    }

    if (unit_literals.find(-lit) != unit_literals.end())
	err(false, "Attempt to assert literal %d.  But, already have %d as unit\n", lit, -lit); {
#if DEBUG
	pwriter->comment("Attempt to assert literal %d.  But, already have %d as unit", lit, -lit);
	pwriter->comment_container("  Current unit literals", unit_literals);
#endif
    }

    report(4, "Asserting literal %d\n", lit);
    unit_literals.insert(lit);
    assigned_literals.push_back(lit);
    context_literal_stack.push_back(lit);
}

void Cnf_reasoner::push_derived_literal(int lit, int cid) {
    if (unit_literals.find(-lit) != unit_literals.end())
	err(false, "Attempt to add unit literal %d.  But, already have derived -%d as unit\n", lit, lit);
    if (unit_literals.find(lit) != unit_literals.end())
	err(false, "Attempt to add unit literal %d.  But, it is already unit\n", lit);
    unit_literals.insert(lit);
    justifying_ids[lit] = cid;
    context_literal_stack.push_back(lit);
}

void Cnf_reasoner::push_clause(int cid, bool force) {
    if (force || cid <= clause_count() || aux_clauses.find(cid) != aux_clauses.end())
	context_clause_stack.push_back(cid);
}

void Cnf_reasoner::pop_context() {
    report(4, "Popping context\n");
    // It's important to first clear the assigned literals
    // and then assign the previously literals.
    // There are cases when both operations are performed for a single
    // literal, and it's important that the net result is to set it to its former value.
    while (true) {
	if (context_literal_stack.size() == 0)
	    err(true, "Tried to pop beyond base of context literal stack\n");
	int lit = context_literal_stack.back(); context_literal_stack.pop_back();
	if (lit == CONTEXT_MARKER)
	    break;
	unit_literals.erase(lit);
	if (auto fid = justifying_ids.find(lit) == justifying_ids.end()) {
	    report(4, "  Removing assertion of literal %d\n", lit);
	    assigned_literals.pop_back();
	} else {
	    justifying_ids.erase(lit);
	    report(4, "  Removing derivation of literal %d\n", lit);
	}
    }
    while (true) {
	if (context_cleared_literal_stack.size() == 0)
	    err(true, "Tried to pop beyond base of context cleared literal stack\n");
	int lit = context_cleared_literal_stack.back(); context_cleared_literal_stack.pop_back();
	if (lit == CONTEXT_MARKER)
	    break;
	report(4, "Reasserting literal %d\n", lit);
	unit_literals.insert(lit);
	assigned_literals.push_back(lit);
    }
    while (true) {
	if (context_clause_stack.size() == 0)
	    err(true, "Tried to pop beyond base of context clause stack\n");
	int cid = context_clause_stack.back(); context_clause_stack.pop_back();
	if (cid == CONTEXT_MARKER)
	    break;
	activate_clause(cid);
	report(4, "  Reactivating clause %d\n", cid);
    }
}

void Cnf_reasoner::clear_assigned_literals() {
    while (assigned_literals.size() > 0) {
	int alit = assigned_literals.back(); assigned_literals.pop_back();
	unit_literals.erase(alit);
	context_cleared_literal_stack.push_back(alit);
	report(4, "Cleared assigned literal %d\n", alit);
    }
}


static void copy_set(std::set<int> *dest, std::set<int> *src) {
    dest->clear();
    for (int v : *src)
	dest->insert(v);
}

void Cnf_reasoner::extract_active_clauses(std::set<int> *save_set) {
    copy_set(save_set, curr_active_clauses);
}

void Cnf_reasoner::set_active_clauses(std::set<int> *new_set) {
    copy_set(curr_active_clauses, new_set);
}


// Partition set of active clauses into subsets, each using distinct sets of variables
// Each set denoted by reference variable
// var2rvar provides a mapping from each variable to the containing set's reference variable
// rvar2cset provides a mapping from the reference variable to the set of clauses
void Cnf_reasoner::partition_clauses(std::unordered_map<int,int> &var2rvar,
				     std::unordered_map<int,std::set<int>*> &rvar2cset) {
    // Simplify clauses
    int ccid = bcp(false);
    if (ccid > 0)
	err(true, "BCP generated conflict on clause %d prior to partitioning\n", ccid);
    // First figure out a partitioning of the variables
    // Map from variable to representative value in its partition
    // Mapping from representative var to set of variables
    var2rvar.clear();
    std::map<int,std::unordered_set<int>*> rvar2vset;
    for (int cid : *curr_active_clauses) {
	Clause *cp = get_clause(cid);
	if (cp->length() < 2)
	    continue;
	for (int i = 0; i < cp->length(); i++) {
	    int lit = (*cp)[i];
	    int var = IABS(lit);
	    if (unit_literals.find(-lit) != unit_literals.end())  {
		// Literal currently falsified
		continue;
	    }
	    if (unit_literals.find(lit) != unit_literals.end())  {
		// Clause satisfied.  This is not expected
		err(true, "Satisfied clause #%d (unit literal %d) found during clause partitionning\n",
		    cid, lit);
		return;
	    }
	    if (var2rvar.find(var) == var2rvar.end()) {
		var2rvar[var] = var;
		std::unordered_set<int> *nset = new std::unordered_set<int>;
		rvar2vset[var] = nset;
		nset->insert(var);
	    }
	}
    }
    for (int cid : *curr_active_clauses) {
	Clause *cp = get_clause(cid);
	for (int i = 0; i < cp->length(); i++) {
	    int lit1 = (*cp)[i];
	    int var1 = IABS(lit1);
	    auto fid1 = var2rvar.find(var1);
	    if (fid1 == var2rvar.end())
		continue;
	    int rvar1 = fid1->second;
	    std::unordered_set<int>*set1 = rvar2vset.find(rvar1)->second;
	    for (int j = i+1; j < cp->length(); j++) {
		int lit2 = (*cp)[j];
		int var2 = IABS(lit2);
		auto fid2 = var2rvar.find(var2);
		if (fid2 == var2rvar.end())
		    continue;
		int rvar2 = fid2->second;
		if (rvar1 != rvar2) {
		    std::unordered_set<int>*set2 = rvar2vset.find(rvar2)->second;
		    // Merge smaller into larger
		    if (set1->size() < set2->size()) {
			std::unordered_set<int>*tset = set1;
			set1 = set2;
			set2 = tset;
			int trvar = rvar1;
			rvar1 = rvar2;
			rvar2 = trvar;
		    }
		    for (int mvar : *set2) {
			set1->insert(mvar);
			var2rvar[mvar] = rvar1;
		    }
		    rvar2vset.erase(rvar2);
		    delete set2;
		}
	    }
	}
    }
    rvar2cset.clear();
    for (auto fid : rvar2vset) {
	int rvar = fid.first;
	// Don't need variable set anymore
	delete fid.second;
	std::set<int> *cset = new std::set<int>;
	rvar2cset[rvar] = cset;
    }
    // Assign clauses to sets
    for (int cid : *curr_active_clauses) {
	Clause *cp = get_clause(cid);
	for (int i = 0; i < cp->length(); i++) {
	    int lit = (*cp)[i];
	    int var = IABS(lit);
	    auto fid = var2rvar.find(var);
	    if (fid == var2rvar.end())
		continue;
	    int rvar = fid->second;
	    std::set<int> *cset = rvar2cset.find(rvar)->second;
	    cset->insert(cid);
	    break;
	}
    }
}

Cnf_reduced *Cnf_reasoner::extract_cnf() {
    Cnf_reduced *rcp = new Cnf_reduced();
    rcp->delete_files = delete_files;
    for (int cid : *curr_active_clauses) {
	Clause *np = get_clause(cid);	
	rcp->add_clause(np, unit_literals, cid);
    }
    return rcp;
}

// Filter out the unit literals that are required for proof, given the main clause and the hint clauses
void Cnf_reasoner::filter_units(Clause *pnp, Clause *php, std::unordered_set<int> &units) {
    units.clear();
    for (int i = 0; i < pnp->length(); i++) {
	int lit = (*pnp)[i];
	if (unit_literals.find(-lit) != unit_literals.end())
	    units.insert(-lit);
    }
    for (int i = 0; i < php->length(); i++) {
	int cid = (*php)[i];
	Clause *hcp = get_clause(cid);
	for (int hi = 0; hi < hcp->length(); hi++) {
	    int lit = (*hcp)[hi];
	    if (unit_literals.find(-lit) != unit_literals.end())
		units.insert(-lit);
	}
    }
}

// Run SAT solver on reduced set of clauses as part of effort to validate literal lit.
// Incorporate generated conflict proof into larger proof
// Return ID of conflict clause
int Cnf_reasoner::reduce_run(int lit) {
    int ncid = 0;
    Cnf_reduced *rcp = extract_cnf();
    std::unordered_set<int> real_units;
    if (rcp->clause_count() >= drat_threshold) {
	if (rcp->run_hinting_solver()) {
	    const char *fname = rcp->get_file_name();
	    pwriter->comment("Adding proof clauses from SAT solver running on file %s to validate literal %d", fname, lit);
	    int pcount = 0;
	    int start_id = clause_count() + proof_clauses.size() + 1;
	    while (true) {
		Clause *php = rcp->get_proof_hint(start_id);
		Clause *pnp = rcp->get_proof_clause(&assigned_literals);
		if (pnp == NULL)
		    break;
		pcount++;
		ncid = start_assertion(pnp);
		// Add extra information about unit literals
		filter_units(pnp, php, real_units);
		for (int ulit : real_units) {
		    auto fid = justifying_ids.find(ulit);
		    if (fid != justifying_ids.end()) {
			int hid = fid->second;
			if (hid != ncid)
			    add_hint(hid);
		    }
		}
		add_hints(php);
		finish_command(true);
		incr_count(COUNT_LITERAL_JUSTIFICATION_CLAUSE);
		delete php;
	    }
	    pwriter->comment("End of proof clauses from SAT solver");
	}
    } else {
	// Want to keep track of range of clauses
	int first_ncid = 0;
	if (rcp->run_solver()) {
	    const char *fname = rcp->get_file_name();
	    pwriter->comment("Adding proof clauses from SAT solver running on file %s to validate literal %d", fname, lit);
	    int pcount = 0;
#if LOG
	    double start = tod();
#endif
	    while (true) {
		Clause *pnp = rcp->get_proof_clause(&assigned_literals);
		if (pnp == NULL)
		    break;
		pcount++;
		ncid = rup_validate(pnp);
		if (first_ncid == 0)
		    first_ncid = ncid;
		if (ncid == 0) {
		    err(false, "SAT solver running on file %s failed to validate proof clause #%d while validating literal %d\n",
			fname, pcount, lit);
		    if (verblevel >= 3)
			pnp->show();
		}
	    }
#if LOG
	    double micro = (tod() - start) * 1e6;
	    log_data("r,%u,%d,%d,%.0f\n", rcp->hash(), rcp->clause_count(), pcount, micro);
#endif
	    pwriter->comment("End of proof clauses from SAT solver running on file %s", fname);
	    // The clauses used in generating this proof are no longer needed
	    for (int cid = first_ncid; cid <= ncid; cid++)
		deactivate_clause(cid);
	} else {
	    const char *fname = rcp->get_file_name();
	    pwriter->comment("SAT solver failed running on file %s to validate literal %d", fname, lit);
	}
    }
    delete rcp;
    return ncid;
}

// Justify that literal holds.  Return ID of justifying clause
// Mode specifies different levels of effort
int Cnf_reasoner::validate_literal(int lit, validation_mode_t mode) {
    auto fid = justifying_ids.find(lit);
    if (fid != justifying_ids.end()) {
#if DEBUG
	pwriter->comment("Literal %d already derived literal, justified by %d", lit, fid->second);
#endif
	return fid->second;
    }
    if (unit_literals.find(lit) != unit_literals.end()) {
#if DEBUG
	pwriter->comment("Literal %d already asserted literal", lit);
#endif
	return 0;
    }

    int ncid = 0;
    new_context();
#if DEBUG
    pwriter->comment("Attempting to validate literal %d by assuming its complement and getting conflict", lit);
#endif
    push_assigned_literal(-lit);
    if (mode != MODE_SAT && bcp_limit > 0) {
	ncid = bcp(mode == MODE_BBCP);
    }
#if DEBUG
    if (ncid != 0)
	pwriter->comment("Validated literal %d via BCP on complement", lit);
    else
	pwriter->comment("Failed to validate literal %d via BCP on complement", lit);
#endif
    if (ncid == 0 && mode != MODE_BCP && mode != MODE_BBCP) {
	ncid = reduce_run(lit);
    }
    pop_context();

    if (ncid != 0 && unit_literals.find(lit) == unit_literals.end()) {
	push_derived_literal(lit, ncid);
    }

    return ncid;
}

// Justify that set of literals hold.
// Justifying clauses IDs are then loaded into jids vector
bool Cnf_reasoner::validate_literals(std::vector<int> &lits, std::vector<int> &jids) {
    jids.resize(lits.size());
    validation_mode_t mode = multi_literal ? MODE_BBCP : MODE_FULL;
    // Which literals can't be handled directly.  Put their negations on list
    ilist args = ilist_new(0);
    // Map them back to positions in lits & jids
    std::unordered_map<int,int> lit2idx;

#if DEBUG
    pwriter->comment_container("Target literals:", lits);
    pwriter->comment_container("Unit literals:", unit_literals);
    pwriter->comment_container("Active clauses:", *curr_active_clauses);
#endif

    // First pass: 
    // In standard mode, validate each literal separately
    // In multi_literal mode, look for easy cases.  Defer the rest
    for (int i = 0; i < lits.size(); i++) {
	int lit = lits[i];
	int jid = validate_literal(lit, mode);
	jids[i] = jid;
	if (jid == 0) {
	    args = ilist_push(args, -lit);
	    lit2idx[-lit] = i;
	}
    }

    int nleft = ilist_length(args);

    if (nleft == 0) {
	ilist_free(args);
	return true;
    }

    if (nleft == 1) {
	// Handle as single literal
	int nlit = args[0];
	int  i = lit2idx.find(nlit)->second;
	jids[i] = validate_literal(-nlit, MODE_FULL);
	bool ok = jids[i] != 0;
	if (!ok)
	    err(false, "Failed to validate literal %d\n", nlit);
	ilist_free(args);
	return ok;
    }

    int defining_cid = find_or_make_aux_clause(args);
    ilist_free(args);
    Clause *anp = get_aux_clause(defining_cid);
    int xvar = -anp->get_activating_literal();

    // Activate conjunction definition
    activate_clause(defining_cid);
    pwriter->comment("Handle %d/%d literals with SAT solver to validate extension variable %d", nleft, lits.size(), xvar);
    report(3, "Handle %d/%d literals with SAT solver to validate extension variable %d\n", nleft, lits.size(), xvar);
    int ncid = validate_literal(xvar, MODE_FULL);
    if (ncid > 0) {
	// Final pass: Target units should be unit or provable with BCP
	for (int i = 0; i < nleft; i++) {
	    int nlit = (*anp)[i];
	    int idx = lit2idx.find(nlit)->second;
	    int jid = quick_validate_literal(-nlit, ncid, defining_cid+i+1);
	    jids[idx] = jid;
	}
	pwriter->comment("Justifications of %d literals completed", nleft);
	deactivate_clause(defining_cid);
	return true;
    } else {
	// Try doing the validations individually
	deactivate_clause(defining_cid);
	err(false, "Couldn't validate literal %d representing conjunction of %d literals.  Try validating individually\n", xvar, nleft);
	for (int i = 0; i < nleft; i++) {
	    int nlit = (*anp)[i];
	    int idx = lit2idx.find(nlit)->second;
	    int jid = validate_literal(-nlit, MODE_FULL);
	    if (jid == 0) {
		err(false, "Failed to validate literal %d\n", nlit);
		lprintf("c  Assigned literals:");
		for (int lit : assigned_literals)
		    lprintf(" %d", lit);
		lprintf("\n");
		lprintf("c  Active clauses:");
		for (int acid : *curr_active_clauses)
		    lprintf(" %d", acid);
		lprintf("\n");
		return false;
	    }
	    jids[idx] = jid;
	}
	return true;
    }
}

void Cnf_reasoner::delete_assertions() {
    // Don't want last one
    pwriter->comment("Delete all but final asserted clause");
    bool remove = false;
    while (deletion_stack.size() > 0) {
	std::vector<int> *dvp = deletion_stack.back();
	if (remove)
	    pwriter->clause_deletion(dvp);
	remove = true;
	delete dvp;
	deletion_stack.pop_back();
    }
}

// Managing set of auxilliary clauses as arguments to lemmas

Clause *Cnf_reasoner::get_aux_clause(int cid) {
    auto fid = aux_clauses.find(cid);
    return fid == aux_clauses.end() ? NULL : fid->second;
}

// Either find an existing auxilliary clause
// or generate one.
// Leaves argument clause untouched.
int Cnf_reasoner::find_or_make_aux_clause(ilist lits) {
    Clause *np = new Clause(lits, ilist_length(lits));
    unsigned h = np->hash();
    auto bucket = aux_clause_lookup.equal_range(h);
    for (auto iter = bucket.first; iter != bucket.second; iter++) {
	int xcid = iter->second;
	Clause *xcp = get_aux_clause(xcid);
	if (xcp == NULL)
	    err(false, "Oops.  Lookup table has clause #%d under hash %u, but no such clause exists\n", xcid, h);
	else if (np->is_equal(xcp)) {
	    if (verblevel >= 3) {
		report(3, "Retrieved existing aux clause %d.  Hash = %u. ", xcid, h);
		xcp->show();
	    }
	    delete np;
	    return xcid;
	}
    }
    // Must create new synthetic clause
    int xvar = new_xvar();
    int len = np->length();
    ilist args = ilist_new(len);
    for (int i = 0 ; i < len; i++)
	args = ilist_push(args, -(*np)[i]);
    incr_count(COUNT_AUX_AND);
    incr_count_by(COUNT_DEFINING_AUX_CLAUSE, len+1);
    int defining_cid = start_and(xvar, args);
    finish_command(false);
    document_and(defining_cid, xvar, args);
    Clause *nnp = new Clause(np);
    nnp->set_activating_literal(-xvar);
    aux_clauses[defining_cid] = nnp;
    aux_clause_lookup.insert({h, defining_cid});
    if (verblevel >= 4) {
	report(4, "Generated new aux clause %d.  Hash = %u. ", defining_cid, h);
	nnp->show();
    }
    return defining_cid;
}

// Lemma support
void Lemma_instance::sign(int xv, bool p_or) {
    next = NULL;
    jid = 0;
    xvar = xv;
    parent_or = p_or;
    unsigned sig = 1;
    sig = next_hash_int(sig, parent_or ? 1 : -1);
    for (auto fid : inverse_cid) {
	int ncid = fid.first;
	sig = next_hash_int(sig, ncid);
    }
    signature = sig;
    jid = 0;
}

// Add active clause to lemma.  It will simplify the clause
// and find/create a synthetic clause to serve as the argument
void Cnf_reasoner::add_lemma_argument(Lemma_instance *lemma, int cid) {
    Clause *np = get_clause(cid);
    ilist slits = np->simplify(unit_literals);
    if (slits == NULL) 
	// Tautology 
	return;
    int ncid = ilist_length(slits) == np->length() ? cid : find_or_make_aux_clause(slits);
    auto fid = lemma->inverse_cid.find(ncid);
    if (fid == lemma->inverse_cid.end()) {
	lemma->inverse_cid[ncid] = cid;
#if DEBUG
	if (ncid == cid)
	    pwriter->comment("  Clause %d used as direct argument", cid);
	else
	    pwriter->comment("  Clause %d serves as proxy for clause %d", ncid, cid);
#endif
    } else if (ncid == cid && fid->second != cid) {
	int ocid = fid->second;
	lemma->duplicate_cid.insert(ocid);
#if DEBUG
	pwriter->comment("  Use clause %d directly, rather than having it be proxy for clause %d", cid, ocid);
#endif
	lemma->inverse_cid[ncid] = cid;
    } else {
	lemma->duplicate_cid.insert(cid);
#if DEBUG
	pwriter->comment("  Don't need clause %d as proxy for clause %d", ncid, cid);
#endif
    }
    ilist_free(slits);
}

Lemma_instance *Cnf_reasoner::extract_lemma(int xvar, bool parent_or) {
    Lemma_instance *lemma = new Lemma_instance;
#if DEBUG
    pwriter->comment("Identifying arguments for lemma at node N%d", xvar);
#endif
    for (int cid : *curr_active_clauses) {
	add_lemma_argument(lemma, cid);
    }
    lemma->sign(xvar, parent_or);
    pwriter->comment("Extracted lemma for node N%d.  Signature %u", xvar, lemma->signature);
    if (lemma->duplicate_cid.size() > 0)
	pwriter->comment_container("  Duplicate clause IDs", lemma->duplicate_cid);
    return lemma;
}

// Set up context for lemma proof
void Cnf_reasoner::setup_proof(Lemma_instance *lemma) {
    new_context();
    clear_assigned_literals();

    report(3, "Proving lemma at N%d\n", lemma->xvar);
#if DEBUG
    int acount = 0;
#endif

    pwriter->comment("Proof of lemma for N%d, signature %u", lemma->xvar, lemma->signature);

    for (auto fid : lemma->inverse_cid) {
	int ncid = fid.first;
	int ocid = fid.second;
	if (ncid != ocid) {
	    deactivate_clause(ocid);
	    activate_clause(ncid);
	}

	Clause *nnp = get_clause(ncid);
	int alit = nnp->get_activating_literal();

	if (alit == 0) {
#if DEBUG
	    acount++;
	    report(3, "  Argument #%d: Clause #%d\n", acount, ncid);
	    pwriter->comment("  Argument #%d: Clause #%d", acount, ncid);
#endif
	} else {
	    push_assigned_literal(alit);
#if DEBUG
	    acount++;
	    report(3, "  Argument #%d: clause #%d.  Activated by literal %d\n", acount, ncid, alit);
	    pwriter->comment("  Argument #%d: clause #%d.  Activated by literal %d", acount, ncid, alit);
#endif
	}
    }
    for (int ocid : lemma->duplicate_cid) {
	deactivate_clause(ocid);
    }
    lemma->jid = 0;
#if DEBUG
    pwriter->comment("Set up to prove lemma for N%d, signature %u", lemma->xvar, lemma->signature);
    pwriter->comment_container("Active clauses:", *curr_active_clauses);
    pwriter->comment_container("Unit literals:", unit_literals);
    if (!check_active()) {
	err(false, "Inconsistent reasoner state\n");
    }
#endif
}

    // Restore context from lemma proof
void Cnf_reasoner::restore_from_proof(Lemma_instance *lemma) {
    for (auto fid : lemma->inverse_cid) {
	int ncid = fid.first;
	int ocid = fid.second;
	if (ncid != ocid) {
	    deactivate_clause(ncid);
	    activate_clause(ocid);
	} 
    }
    pop_context();
    for (int ocid : lemma->duplicate_cid) {
	activate_clause(ocid);
	incr_count(COUNT_LEMMA_ARGUMENT_MERGE);
    }
#if DEBUG
    pwriter->comment("Restoring context after proving lemma for N%d, signature %u", lemma->xvar, lemma->signature);
    pwriter->comment_container("Active clauses:", *curr_active_clauses);
    pwriter->comment_container("Unit literals:", unit_literals);
    if (!check_active()) {
	err(false, "Inconsistent reasoner state\n");
    }
#endif

}

int Cnf_reasoner::apply_lemma(Lemma_instance *lemma, Lemma_instance *instance) {
    // Make sure they're compatible
    // Should have identical sets of new clause IDs
    bool ok = true;
    if (lemma->parent_or != instance->parent_or) {
	err(false, "Attempting to apply lemma for node N%d.  Lemma and instance differ on type of parenthood\n", lemma->xvar);
	ok = false;
    }
    for (auto lfid : lemma->inverse_cid) {
	if (!ok)
	    break;
	int ncid = lfid.first;
	if (instance->inverse_cid.find(ncid) == instance->inverse_cid.end()) {
	    err(false, "Attempting to apply lemma for node N%d.  Lemma argument clause #%d not found in instance\n", lemma->xvar, ncid);
	    ok = false;
	}
    }
    for (auto ifid : instance->inverse_cid) {
	if (!ok)
	    break;
	int ncid = ifid.first;
	if (lemma->inverse_cid.find(ncid) == lemma->inverse_cid.end()) {
	    err(false, "Attempting to apply lemma for node N%d.  Instance argument clause #%d not found in lemma\n", lemma->xvar, ncid);
	    ok = false;
	}
    }
    if (!ok)
	return 0;
    // Now justify lemma arguments
    std::vector<int> arg_jids;
    pwriter->comment("Application of lemma for N%d, signature %u", lemma->xvar, lemma->signature);
#if DEBUG
    pwriter->comment_container("Assigned literals:", assigned_literals);
    pwriter->comment_container("Unit literals:", unit_literals);
#endif
    int acount = 0;
    for (auto ifid : instance->inverse_cid) {
	int ocid = ifid.second;
	int ncid = ifid.first;
	if (ocid == ncid) {
	    pwriter->comment("  Arg %d.  Clause #%d used directly", ++acount, ocid);
#if DEBUG
	    // Double check
	    Clause *anp = get_clause(ncid);
	    int alit = anp->get_activating_literal();
	    if (alit != 0 && unit_literals.find(alit) == unit_literals.end()) {
		pwriter->diagnose("Couldn't apply lemma N%d, signature %u", lemma->xvar, lemma->signature);
		pwriter->diagnose("Clause #%d used directly in lemma, but activating literal %d not unit",
				  ncid, alit);
		return 0;
	    }
#endif	  
	    continue;
	}
	Clause *anp = get_clause(ncid);
	int alit = anp->get_activating_literal();
	if (unit_literals.find(alit) != unit_literals.end()) { 
	    pwriter->comment("  Arg %d.  Clause #%d replaced by #%d, which is already unit", ++acount, ocid, ncid);
	    auto fid = justifying_ids.find(alit);
	    if (fid != justifying_ids.end())
		arg_jids.push_back(fid->second);
	} else {
	    Clause *nnp = new Clause();
	    nnp->add(alit);
	    for (int lit : assigned_literals)
		nnp->add(-lit);
	    pwriter->comment("  Arg %d.  Clause #%d replaced by #%d", ++acount, ocid, ncid);
	    int ccid = start_assertion(nnp);
	    arg_jids.push_back(ccid);
	    // Add hints from synthetic clause definition
	    for (int offset = 1; offset <= anp->length(); offset++)
		add_hint(ncid+offset);
	    // Add hints based on context
	    Clause *cnp = get_clause(ocid);
	    for (int i = 0; i < cnp->length(); i++) {
		int clit = (*cnp)[i];
		auto fid = justifying_ids.find(-clit);
		if (fid != justifying_ids.end())
		    add_hint(fid->second);
	    }
	    add_hint(ocid);
	    finish_command(true);
	    incr_count(COUNT_LEMMA_APPLICATION_CLAUSE);
	    delete nnp;
	}
    }
    // Finally, assert the root
    Clause *lnp = new Clause();
    lnp->add(lemma->xvar);
    for (int lit : assigned_literals)
	lnp->add(-lit);
    pwriter->comment("Justification of lemma root %d in context", lemma->xvar);
    int jid = start_assertion(lnp);
    for (int ajid : arg_jids)
	add_hint(ajid);
    add_hint(lemma->jid);
    finish_command(true);
    incr_count(COUNT_LEMMA_APPLICATION_CLAUSE);
    delete lnp;
    return jid;
}

// Debugging support
bool Cnf_reasoner::check_active() {
    bool ok = true;
#if DEBUG
    for (int cid : *curr_active_clauses) {
	if (cid > clause_count()) {
	    Clause *nnp = get_clause(cid);
	    int alit = nnp->get_activating_literal();
	    if (alit != 0 && unit_literals.find(alit) == unit_literals.end()) {
		pwriter->diagnose("Lost track of activating literal %d for active clause #%d", alit, cid);
		ok = false;
		break;
	    }
	}
    }
#endif
    return ok;
}

int Cnf_reasoner::monolithic_validate_root(int root_literal) {
    const char *cnf_name = "cpog_validation_xxx.cnf";
    const char *lrat_name = "cpog_validation_xxx.lrat";
    char cmd[350];

    FILE *cnf_out = fopen(cnf_name, "w");
    if (!cnf_out) {
	err(true, "Couldn't open temporary file '%s'\n", cnf_name);
    }
    int starting_proof_size = proof_clauses.size();
    int full_clause_count = clause_count() + starting_proof_size;
    // Write Input clauses + initial BCP clauses + defining clauses as CNF
    fprintf(cnf_out, "p cnf %d %d\n", xvar_count, full_clause_count);
    for (int cid = 1; cid <= full_clause_count; cid++) {
	Clause *clp = get_clause(cid);
	clp->show_reduced(cnf_out, -root_literal);
    }
    fclose(cnf_out);
    
    double start = tod();
    snprintf(cmd, 350, "cadical --no-binary --unsat -q %s - | drat-trim %s -L %s > /dev/null", cnf_name, cnf_name, lrat_name);
    int rc = system(cmd);
    incr_timer(TIME_SAT, tod()-start);
    if (rc != 0) {
	err(false, "Executing command '%s' yielded return code %d\n", cmd, rc);
	return 0;
    }
    FILE *lfile = fopen(lrat_name, "r");
    if (!lfile) {
	err(false, "Couldn't open generated LRAT file\n", lrat_name);
	return 0;
    }
    if (!monolithic_load_proof(lfile, root_literal)) {
	err(false, "Failed to read generated LRAT file\n", lrat_name);
	return 0;
    }
    fclose(lfile);
    Clause *lnp = proof_clauses.back();
    if (lnp->length() != 1) {
	err(false, "Execution of command '%s' did not generate unit clause\n", cmd);	
	return false;
    }
    int nclauses = proof_clauses.size() - starting_proof_size;
    report(3, "Drat-trim.  %s %d problem clauses.  Added %d proof clauses\n", cnf_name, full_clause_count, nclauses); 
    incr_histo(HISTO_PROBLEM, full_clause_count);
    incr_histo(HISTO_PROOF, nclauses);

    if (delete_files) {
	remove(cnf_name);
	remove(lrat_name);
    }
    return clause_count() + proof_clauses.size();
}
 
bool Cnf_reasoner::monolithic_load_proof(FILE *lfile, int root_literal) {
    pwriter->comment("Monolithic proof of root literal %d", root_literal);
    int nclause = clause_count() + proof_clauses.size();
    std::unordered_map<int,int> lrat2local;
    int next_id = nclause + 1;
    while (find_token(lfile)) {
	int sid = 0;
	if (fscanf(lfile, "%d", &sid) != 1) {
	    err(false, "Couldn't read step Id in LRAT file.  Should be at step #%d\n", next_id);
	    return false;
	}
	if (!find_token(lfile)) {
	    err(false, "EOF found while trying to parse proof step #%d\n", next_id);
	}
	int c = getc(lfile);
	if (c == EOF) {
	    err(false, "EOF found while trying to parse proof step #%d\n", sid);
	    return false;
	}
	if (c == 'd') {
	    c = skip_line(lfile);
	    if (c == EOF) {
		err(false, "EOF found while trying to parse proof step #%d\n", sid);
		return false;
	    }
	    ungetc(c, lfile);
	    continue;
	} else
	    ungetc(c, lfile);
	// Here's the good stuff
	bool eof;
	Clause *np = new Clause(lfile, true, &eof);
	if (np == NULL || eof) {
	    err(false, "Error encountered while trying to read literals from proof step #%d\n", sid);
	    return false;
	}
	// Add root literal
	np->add(root_literal);
	Clause *hp = new Clause(lfile, true, &eof);
	if (hp == NULL || eof) {
	    err(false, "Error encountered while trying to read hints from proof step #%d\n", sid);
	    return false;
	}
	lrat2local[sid] = next_id;
	// Fix up hints
	for (int i = 0; i < hp->length(); i++) {
	    int hint = (*hp)[i];
	    int nhint = (hint <= nclause) ? hint : lrat2local.find(hint)->second;
	    (*hp)[i] = nhint;
	}
	start_assertion(np);
	add_hints(hp);
	finish_command(true);

	incr_count(COUNT_MONOLITHIC_CLAUSE);
	next_id++;
    }
    return true;
}
