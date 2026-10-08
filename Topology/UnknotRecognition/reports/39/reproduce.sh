#!/bin/sh
set -eu
cd "$(dirname "$0")"
export PYTHONPATH="$(pwd)/code${PYTHONPATH:+:$PYTHONPATH}"
python -m unittest discover -s tests -v > data/unit_tests.txt 2>&1
python experiments/validate_independent.py > data/independent_validation.txt 2>&1
python experiments/benchmark.py > data/benchmark_output.txt 2>&1
python experiments/make_artifacts.py
sh build.sh
printf 'Reproduced local checks, new machine-specific measurements, and article.\n'
