#!/bin/bash
set -e
# Process an opam.pins file from stdin.

while read PACKAGE PIN; do
    if echo "$PIN" | egrep '^https://gitlab\.mpi-sws\.org' > /dev/null; then
        # an MPI URL -- try doing recursive pin processing
        URL=$(echo "$PIN" | sed 's|#|/raw/|')/opam.pins
        curl -f "$URL" 2> /dev/null | "$0"
    fi
    echo "Applying pin: $PACKAGE -> $PIN"
    opam pin add "$PACKAGE" "$PIN" -k git -y -n
done
