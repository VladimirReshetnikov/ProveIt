#!/bin/sh
set -eu
cd "$(dirname "$0")"
export PYTHONPATH="$PWD/src:$PWD/reference_upstream${PYTHONPATH:+:$PYTHONPATH}"
python -m unittest discover -s tests -v
python experiments/audit.py
python experiments/benchmark.py
python experiments/verify_examples.py
sh article/build.sh
