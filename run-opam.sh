#!/usr/bin/env bash
set -ve
# Setting up dependencies by installing SSProve via opam.
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam pin add coq-ssprove https://github.com/SSProve/ssprove.git#v0.3.1
# Compiling the Rocq project by using make.
make -j 3
# Success!
