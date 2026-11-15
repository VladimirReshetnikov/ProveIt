#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"

echo '[1/4] exact polynomial certificates'
python3 verify_morley_identities.py
python3 -m json.tool morley_identity_certificate.json >/dev/null
python3 -m json.tool morley_certificate_schema.json >/dev/null

echo '[2/4] Python syntax'
python3 -m py_compile verify_morley_identities.py

echo '[3/4] LaTeX/PDF'
if command -v pdflatex >/dev/null 2>&1; then
  for _ in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error morley_ipra.tex >/dev/null
  done
  pdfinfo morley_ipra.pdf | grep -E '^(Pages|Encrypted|Page size):'
else
  echo 'pdflatex not installed; skipped PDF rebuild' >&2
fi

echo '[4/4] Lean'
if command -v lean >/dev/null 2>&1; then
  lean MorleyAlgebra.lean
else
  echo 'Lean not installed; candidate Lean files were not compiled' >&2
fi

echo 'artifact checks completed'
