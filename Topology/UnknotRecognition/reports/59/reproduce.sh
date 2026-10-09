#!/bin/sh
set -eu
cd "$(dirname "$0")"
python -m unittest discover -s tests -v
python benchmarks/run_benchmarks.py --output results/benchmarks_rerun.json
# The retained article uses benchmarks.json, not an unreviewed timing rerun.
python benchmarks/make_tables.py
(cd article && sh build.sh)
