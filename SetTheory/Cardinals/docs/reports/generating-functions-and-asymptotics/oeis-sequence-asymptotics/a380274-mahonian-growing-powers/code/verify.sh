#!/bin/sh
set -eu
cd "$(dirname "$0")"
mkdir -p receipts
python3 derive_coefficients.py > coefficients.txt
python3 check_crossover.py > receipts/producer_checks.txt
python3 audit_independent.py > receipts/independent_checks.txt
python3 verify_results.py
