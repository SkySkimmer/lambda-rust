# LAMBDA-RUST COQ DEVELOPMENT

This is the Coq formalization of lambda-Rust.

## Prerequisites

This version is known to compile with:

 - Coq 8.5pl3
 - Ssreflect 1.6
 - A development version of [Iris](https://gitlab.mpi-sws.org/FP/iris-coq/)

The easiest way to install the correct versions of the dependencies is through
opam.  Once you got opam set up, just run `make build-dep` to install the right
versions of the dependencies.  When the dependencies change (e.g., a newer
version of Iris is needed), just run `make build-dep` again.

Alternatively, you can manually determine the required Iris commit by consulting
the `opam.pins` file.

## Building Instructions

Run `make` to build the full development.

## For Developers: How to update the Iris dependency

- Do the change in Iris, push it.
- In lambdaRust, change opam.pins to point to the new commit.
- Run "make build-dep" (in lambdaRust) to install the new version of Iris.
- You may have to do "make clean" as Coq will likely complain about .vo file
  mismatches.
