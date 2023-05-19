## CPOG Knowledge Compiler Certifier

This repository contains a set of tools for certifying results from the D4 knowledge
compiler.  It is based on the **CPOG** verification framework.  A CPOG file
encodes both a representation of a Boolean formula as a
**partitioned-operation graph** (POG), and a proof that this POG is
logically equivalent to the input formula

# Installation:

Running the toolchain using prototype (unverified) tools requires the following:

* A C and C++ compiler
* A python3 interpreter
* An installed version of the [D4 knowledge compiler](https://github.com/crillab/d4)
* An installed version of the [CaDiCal SAT solver](https://github.com/arminbiere/cadical)
* An installed version of the [Drat-trim proof checker](https://github.com/marijnheule/drat-trim)

In addition, running the toolchain using formally verified tools requires the following:

* An installed version of the Lean [Elan version manager](https://github.com/leanprover/elan)

# Directories

* **VerifiedChecker:**
    Code for the verified checker and counter
* **benchmarks:**
    A sample set of benchmarks from the 2022 standard and weighted model counting competitions
* **src:**
    Code for the CPOG generator and prototype checker
* **test:**
    Two very simple test problems
* **tools:**
    Code for a scripting program that runs the entire toolchain


# Make Options

* **install:**
    Compiles the CPOG generator and prototype checker.
* **linstall:**
    Compiles the Lean verifier
* **ptest:**
    Runs the prototype tools on two simple test problems
* **ltest:**
    Runs the verified tools on two simple test problems
* **run:**
    Runs the generator, prototype checker, and prototype counter on 30 benchmark files
* **lrun:**
    Runs the verified checker/counter on 30 benchmark files
* **clean:**
    Removes intermediate files
* **superclean:**
    Removes all generated files
