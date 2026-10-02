#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p results
bash code/run_checks.sh --output-dir "$PWD/results"
bash build_pdf.sh
printf 'PASS: exact, symbolic, numerical, inversion, and PDF rebuild checks\n'
