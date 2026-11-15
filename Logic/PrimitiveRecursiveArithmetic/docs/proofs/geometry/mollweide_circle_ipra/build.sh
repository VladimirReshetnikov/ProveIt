#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"

mkdir -p verification
python3 -m py_compile verification/check_identities.py
python3 verification/check_identities.py | tee verification/certificate_report.txt
latexmk -pdf -interaction=nonstopmode -halt-on-error mollweide_circle_ipra.tex \
  | tee verification/latex_build.txt
pdfinfo mollweide_circle_ipra.pdf > verification/pdfinfo.txt
pdffonts mollweide_circle_ipra.pdf > verification/pdffonts.txt

printf '\nBuild complete.\n'
printf '  PDF: %s\n' "$PWD/mollweide_circle_ipra.pdf"
printf '  Verification: %s\n' "$PWD/verification/results.json"
