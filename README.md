# LAMBDA-RUST COQ DEVELOPMENT

This is the Coq development accompanying lambda-Rust.

## Prerequisites

This version is known to compile with:

 - Coq 8.6.1
 - Ssreflect 1.6.1
 - A development version of [Iris](https://gitlab.mpi-sws.org/FP/iris-coq/)

The easiest way to install the correct versions of the dependencies is through
opam.  You will need the Coq and Iris opam repositories:

    opam repo add coq-released https://coq.inria.fr/opam/released
    opam repo add iris-dev https://gitlab.mpi-sws.org/FP/opam-dev.git

Once you got opam set up, run `make build-dep` to install the right versions
of the dependencies.  When the dependencies change, just run `make build-dep`
again.

## Building Instructions

Run `make` to build the full development.

## Structure

* The folder [lang](theories/lang) contains the formalization of the lambda-Rust
  core language, including the theorem showing that programs with data races get
  stuck.
* The folder [lifetime](theories/lifetime) proves the rules of the lifetime
  logic, including derived constructions like (non-)atomic persistent borrows.
* The folder [typing](theories/typing) defines the domain of semantic types,
  interpretations of all the judgments, as well as proofs of all typing rules.
  * The subfolder [examples](theories/typing/examples) shows how the examples
    from the technical appendix can be type-checked in Coq.
  * The subfolder [lib](theories/typing/lib) contains proofs of safety of some
    unsafely implement types from the Rust standard library and some user
    crates: `Cell`, `RefCell`, `Rc`, `Arc`, `Mutex`, `RwLock`, `mem::swap`,
    `thread::spawn`, `take_mut::take`, `alias::once` as well as converting `&&T`
    to `&Box<T>`.

## For Developers: How to update the Iris dependency

* Do the change in Iris, push it.
* In lambdaRust, change opam.pins to point to the new commit.
* Run "make build-dep" (in lambdaRust) to install the new version of Iris.
* You may have to do "make clean" as Coq will likely complain about .vo file
  mismatches.
