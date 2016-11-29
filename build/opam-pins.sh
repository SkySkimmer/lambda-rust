#!/bin/bash
set -e
## Process an opam.pins file from stdin: Apply the pins and install the packages.
## Usage:  (Arguments have to be given in the given order!)
##   ./opam-pins.sh [--recursive]
## Arguments:
##   -- recursive    This is a recurisve call of the script to itself
##                   (you should not pass this argument yourself manually).


# Parse arguments
if [[ "$1" == "--recursive" ]]; then
    shift
    IS_TOPLEVEL=0
else
    # We are the toplevel call. Record the old pin state.
    IS_TOPLEVEL=1
    OLD_PINS="$(mktemp)"
    opam pin list > "$OLD_PINS"
fi

if [[ "$1" == "-n" ]]; then
    shift
    NFLAG="-n"
else
    NFLAG=""
fi

# Process stdin
while read PACKAGE PIN; do
    if echo "$PIN" | egrep '^https://gitlab\.mpi-sws\.org' > /dev/null; then
        # an MPI URL -- try doing recursive pin processing
        URL=$(echo "$PIN" | sed 's|#|/raw/|')/opam.pins
        curl -f "$URL" 2> /dev/null | "$0" --recursive
    fi
    echo "[opam-pins] Applying pin: $PACKAGE -> $PIN"
    opam pin add "$PACKAGE" "$PIN" -k git -y -n
    echo
done

# If we are the toplevel call, see what pins changed and reinstall if necessary
if [[ "$IS_TOPLEVEL" == "1" ]]; then
    NEW_PINS="$(mktemp)"
    opam pin list > "$NEW_PINS"
    # Compare the pin lists and filter for the changed package names
    PACKAGES=$(diff -u0 "$OLD_PINS" "$NEW_PINS" | egrep '^[+][^+]' | sed 's/+\([a-z0-9-]\+\)[ .].*$/\1/')
    if [[ -n "$PACKAGES" ]]; then
        echo "[opam-pins] Reinstalling packages:" $PACKAGES
        opam reinstall $PACKAGES -y
    fi
    rm "$OLD_PINS" "$NEW_PINS"
fi
