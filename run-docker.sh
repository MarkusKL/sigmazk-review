#!/usr/bin/env bash
set -ve
# Setting up dependencies by building a docker image.
docker build -t review-sigmazk .
# Compiling the Rocq project by using make in a nix-shell in the container.
docker run --rm -it review-sigmazk --run "make -j 3"
# Success!
