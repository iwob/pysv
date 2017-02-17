#!/usr/bin/env bash

PDIR=$(pwd)
mkdir -p solvers_bin
mkdir -p solvers_bin/tmp
cd solvers_bin/tmp
git clone https://github.com/Z3Prover/z3 -b master
cd z3
python scripts/mk_make.py
cd build
make all
cp z3 $PDIR/solvers_bin
