#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
python3 code/verify_constants.py
python3 demo/complex_spectra_demo.py --height 40 --output demo --reuse-roots
python3 demo/verify_saved_data.py
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
