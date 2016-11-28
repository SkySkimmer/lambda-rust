# LAMBDA-RUST COQ DEVELOPMENT

This is the Coq formalization of lambda-Rust.

## Prerequisites

This version is known to compile with:

 - Coq 8.5pl3
 - Ssreflect 1.6
 - A development version of [Iris](https://gitlab.mpi-sws.org/FP/iris-coq/)

The easiest way to install the correct versions of the dependencies is through
opam.  Once you got opam set up, just run `make build-dep` to install the right
versions of the dependencies.

Alternatively, you can manually determine the required Iris commit by consulting
the `opam.pins` file.

## Building Instructions

Run `make` to build the full development.
