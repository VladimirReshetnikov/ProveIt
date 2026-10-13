#!/bin/sh
set -eu
cd "$(dirname "$0")"
python -m unittest discover -s tests -v
python -m experiments.validate
python -m experiments.benchmark
python -m experiments.render_tables
sh article/build.sh
