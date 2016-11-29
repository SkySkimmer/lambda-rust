#!/bin/bash
set -e
# This script installs the build dependencies for CI builds.

# Prepare OPAM configuration
export OPAMROOT="$(pwd)/opamroot"
export OPAMJOBS=16
export OPAM_EDITOR="$(which false)"

# Make sure we got a good OPAM
test -d "$OPAMROOT" || (mkdir "$OPAMROOT" && opam init -n)
eval `opam conf env`
test -d "$OPAMROOT/repo/coq-extra-dev" || opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev -p 5
test -d "$OPAMROOT/repo/coq-core-dev" || opam repo add coq-core-dev https://coq.inria.fr/opam/core-dev -p 5
test -d "$OPAMROOT/repo/coq-released" || opam repo add coq-released https://coq.inria.fr/opam/released -p 10
opam update
opam install ocamlfind -y # Remove this once the Coq crew fixed their package...

# Pick fixed versions of some dependencies
echo
for PIN in "${@}"
do
    echo "Applying pin: $PIN"
    opam pin add $PIN -k version -y -n
done

# Install/upgrade build-dependencies
echo
opam upgrade -y
make build-dep Y=1

# done
echo
coqc -v
