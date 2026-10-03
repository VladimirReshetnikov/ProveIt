#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
python check_a122399.py > test_output.txt
python export_exact_coefficients.py
python verify_contour_inverse.py > contour_inverse_output.txt
python verify_congruences.py
python make_report.py
bash build.sh
if [[ "${RUN_INDEPENDENT_AUDIT:-1}" == 1 ]]; then
  python audit/independent_audit.py > audit/independent_audit_output.txt
fi
printf 'PASS: full A122399 producer replay, PDF build, and requested audit replay\n'
