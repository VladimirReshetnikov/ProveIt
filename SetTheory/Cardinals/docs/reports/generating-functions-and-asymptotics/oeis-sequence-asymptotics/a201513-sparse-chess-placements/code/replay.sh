#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
python compute_clusters.py --order 6
python derive_expansion.py
python verify_finite.py > finite_verification.txt
python independent_verification/check_coefficients.py
