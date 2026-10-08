#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p results
python -m unittest discover -s tests -v 2>&1 | tee results/unit_tests.txt
python experiments/validate_algebra.py | tee results/algebra_validation_console.txt
python experiments/validate_braids.py | tee results/braid_validation_console.txt
python experiments/validate_marked.py | tee results/marked_validation_console.txt
python experiments/benchmark.py | tee results/benchmark_console.txt
python experiments/make_tables.py
if command -v pdflatex >/dev/null 2>&1; then
  make paper
else
  printf '%s\n' 'Mathematical checks complete. pdfLaTeX is needed to rebuild the paper.'
fi
