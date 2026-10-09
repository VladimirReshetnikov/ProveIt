#!/bin/sh
set -eu
cd "$(dirname "$0")"
python -m unittest discover -s tests -v > results/unit-tests.txt 2>&1
python experiments/run_audit.py > results/audit-progress.txt
python experiments/benchmark.py > results/benchmark-progress.txt
python experiments/generate_examples.py
python experiments/render_tables.py
sh paper/build.sh
printf '%s\n' 'Reproduction complete. Timings and rebuilt PDF may change checksums.'
