#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
export PYTHONHASHSEED=0
export PYTHONDONTWRITEBYTECODE=1
python residue_expansion.py > residue-output.txt
python saddle_expansion.py > saddle-output.txt
python verify_coefficients.py > coefficient-output.txt
python verify_spectral_moments.py > spectral-output.txt
python verify_inverse.py > inverse-output.txt
./build.sh
printf 'All symbolic and numerical checks and the PDF build completed.\n'
