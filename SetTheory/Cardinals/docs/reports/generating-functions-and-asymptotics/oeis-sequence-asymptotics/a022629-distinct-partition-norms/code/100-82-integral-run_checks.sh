#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
python -O checks/check_formal_series.py
python -O checks/check_coefficients_independent.py
