#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p data
python3 code/derive.py > data/coefficients.txt
python3 code/verify.py > data/verify_summary.json
cat data/verify_summary.json
