#!/usr/bin/env bash
set -ve
# Setting up dependencies.
nix-shell --run :
# Compiling the Rocq project by using make in the nix-shell.
nix-shell --run "make -j 3"
# Success!
