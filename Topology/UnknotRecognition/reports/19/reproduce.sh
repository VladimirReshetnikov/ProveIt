#!/bin/sh
set -eu
cd "$(dirname "$0")"
export PYTHONPATH="$PWD/src${PYTHONPATH:+:$PYTHONPATH}"
python -m unittest discover -s tests -v
python experiments/validate.py groups
python experiments/validate.py optimality
python experiments/validate.py independent
python experiments/benchmark.py
python -m ranktwo compress examples/sleeved_unknot_4_16.json --passes 1 --output results/example_compressed.json
python -m ranktwo verify examples/sleeved_unknot_4_16.json results/example_compressed.json
