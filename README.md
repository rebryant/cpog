## CRAT

This repository contains a set of tools for certifying the D4 model
counter.  It is based on the CRAT verification framework.  A CRAT file
encodes both a representation of a Boolean formula as a
*partitioned-operation graph* (POG), and a proof that this POG is
logically equivalent to the input formula

# Installation:

Running the toolchain requires the following:

* A C and C++ compiler
* A python3 interpreter
* An installed version of the [D4 knowledge compiler](https:://github.com/crillab/d4))
* An installed version of the [Cadical SAT solver](https://github.com/arminbiere/cadical)
* An installed version of the drat-trim [DRAT proof checker](https://github.com/marijnheule/drat-trim)
* An installed verions of the Lean [elan version manager](https://github.com/leanprover/elan)

# Directories

* VerifiedChecker:
    Code for the verified checker and counter
* benchmarks:
    A sample set of benchmarks from the 2022 standard and weighted model counting competitions
* src:
    Code for the CRAT generator and prototype checker
* test:
    Two very simple test problems
* tools:
    Code for the prototype counter and for a program to run the entire toolchain


# Make Options

* install:
    Compiles the CRAT generator, prototype checker, and the Lean verifier
* run:
    Runs the generator, prototype checker, and prototype counter on 34 benchmark files
* lrun:
    Runs the verified checker/counter on 34 benchmark files
* clean:
    Removes intermediate files
* superclean:
    Removes all generated files

    