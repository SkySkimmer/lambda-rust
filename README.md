# LAMBDA-RUST COQ DEVELOPMENT

This is the Coq formalization of lambda-Rust.

## Prerequisites

This version is known to compile with:

 - Coq 8.5pl2
 - Ssreflect 1.6

You will furthermore need an up-to-date version of
[Iris](https://gitlab.mpi-sws.org/FP/iris-coq/).  Run `git submodule status` to
see which git commit of Iris is known to work.  You can pick between using a
system-installed Iris (from Coq's `user-contrib`) or a version of Iris locally
compiled for lambda-Rust.

## Building Instructions

To use the system-installed Iris (which is the default), run `make iris-system`.
This only works if you previously built and installed a compatible version of the
Iris Coq formalization.  To use a local Iris (which will always be the right
version), run `make iris-local`.  Run this command again later to update the
local Iris, in case the preferred Iris version changed.

Now run `make` to build the full development.
