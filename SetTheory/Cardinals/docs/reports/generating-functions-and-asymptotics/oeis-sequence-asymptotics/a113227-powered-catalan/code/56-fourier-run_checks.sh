#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
python residue_expansion.py > residue-output.txt
python saddle_expansion.py > saddle-output.txt
python verify_fourier_sectors.py > fourier-output.txt
python verify_fourier_sectors.py --order 192 --output quadrature_refinement_diagnostics.json > quadrature-refinement-output.txt
python verify_exponential_spectral_replacement.py > spectral-replacement-output.txt
python verify_output_consistency.py > consistency-output.txt
bash build.sh
