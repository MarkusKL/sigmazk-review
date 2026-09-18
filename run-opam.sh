#!/usr/bin/env bash
set -ve
# Setting up dependencies by installing SSProve via opam.
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam pin add coq-ssprove https://github.com/SSProve/ssprove.git#9b14e90
# Compiling the Rocq project by using make.
make -j 3
# Success!
