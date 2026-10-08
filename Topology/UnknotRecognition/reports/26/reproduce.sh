#!/bin/sh
set -eu
cd "$(dirname "$0")"
export PYTHONPATH=".$(test -z "${PYTHONPATH:-}" || printf :%s "$PYTHONPATH")"
python -m unittest discover -s tests -v
python experiments/validate.py
python experiments/benchmark.py
# The commands above overwrite their JSON records with a fresh local run.
# The PDF deliberately records the delivered run, not automatically new timings.
