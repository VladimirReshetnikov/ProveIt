#!/bin/sh
set -eu
cd "$(dirname "$0")"
if [ "${1:-}" != "" ] && [ "$1" != "--bench" ]; then
  echo "Usage: sh reproduce.sh [--bench]" >&2
  exit 2
fi
python -m unittest discover -s tests -v
python experiments/validate.py
python experiments/cost_certificates.py
python experiments/hierarchy_budget.py
if [ "${1:-}" = "--bench" ]; then
  python experiments/benchmark.py --rounds 7
  python experiments/ablate_runs.py
fi
