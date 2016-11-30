#!/bin/bash
set -e
## Process an opam.pins file from stdin: Add all the given pins, but don't install anything.
## Usage:
##   ./opam-pins.sh < opam.pins

# Process stdin
while read PACKAGE URL HASH; do
    if echo "$URL" | egrep '^https://gitlab\.mpi-sws\.org' > /dev/null; then
        echo "[opam-pins] Recursing into $URL"
        # an MPI URL -- try doing recursive pin processing
        curl -f "$URL/raw/$HASH" 2> /dev/null | "$0"
    fi
    echo "[opam-pins] Applying pin: $PACKAGE -> $URL#$HASH"
    opam pin add "$PACKAGE.dev.$HASH" "$URL#$HASH" -k git -y -n
    echo
done
