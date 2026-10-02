#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
python verify_reduction.py > exact-replay.log
python independent_checks.py > independent-replay.log
COMBINING_D=2 python derive_coefficients.py --order 6 > coefficients-d2.log
COMBINING_D=3 python derive_coefficients.py --order 6 > coefficients-d3.log
python numerical_diagnostic.py > numerical-diagnostics.log
