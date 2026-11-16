#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
python3 code/generate_coverage_table.py
python3 code/exact_coefficient_checks.py
python3 code/numerical_special_cases.py
python3 code/coverage_summary.py
