#!/bin/sh
set -eu
cd "$(dirname "$0")"
mkdir -p results
python -m unittest discover -s tests -v > results/unittest.log 2>&1
python -m experiments.validation > results/validation.log
python -m experiments.benchmark --repeats 3 > results/benchmark.log
sh article/build.sh
