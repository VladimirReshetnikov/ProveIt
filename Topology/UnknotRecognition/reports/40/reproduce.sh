#!/bin/sh
set -eu
cd "$(dirname "$0")"
export PYTHONPATH="$PWD/src${PYTHONPATH:+:$PYTHONPATH}"
python -m unittest discover -s tests -v > data/unit-tests.txt 2>&1
python scripts/validate.py > data/validation-console.txt
python scripts/benchmark.py > data/benchmark-console.txt
python scripts/make_tables.py
sh build.sh
# Timing-dependent data have now changed; regenerate hashes before redistributing.
python scripts/checksums.py --write
