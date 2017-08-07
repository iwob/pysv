In this directory you can put binaries (or symbolic links) of any SMT-solver and easily
use it for synthesis or verification of python programs. Solvers must be compatible with
SMT-LIB 2.0 language.


Download links for binary distributions of some SMT solvers:
* Z3
    https://github.com/Z3Prover/z3/releases
    (building the newest version (repository's head on master) from source is recommended)
* CVC4
    http://cvc4.cs.stanford.edu/web/
* MathSAT
    http://mathsat.fbk.eu/download.html


To easily use the solver simply move it's binary to this folder (solvers-bin). This is where by
default solvers binaries are looked for. Default names of the solvers binaries (as well as
names for --solver option) are:

* Z3: z3
* CVC4: cvc4
* MathSAT: mathsat

If you name binaries like specified above you will not have to explicitly specify path to the
solver - it will suffice to provide it's name (e.g. "--solver z3"). z3 is the default, so if
you want to use other solver you need to change this option accordingly.
