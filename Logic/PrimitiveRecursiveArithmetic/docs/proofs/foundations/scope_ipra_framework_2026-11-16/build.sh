#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd)"

cd "$ROOT/reference"
python3 -m unittest -v test_scope_reference.py 2>&1 | tee "$ROOT/validation/python_tests.txt"
python3 scope_reference.py --demo "$ROOT/examples/demo_certificate.json"

cd "$ROOT"
if command -v latexmk >/dev/null 2>&1; then
  latexmk -pdf -interaction=nonstopmode -halt-on-error scope_ipra_framework.tex \
    | tee validation/latex_build.txt
  latexmk -c scope_ipra_framework.tex >/dev/null
elif [[ -f /home/oai/skills/pdfs/scripts/latex_to_pdf.py ]]; then
  python /home/oai/skills/pdfs/scripts/latex_to_pdf.py \
    scope_ipra_framework.tex -o scope_ipra_framework.pdf \
    | tee validation/latex_build.txt
else
  echo "No latexmk or PDF conversion helper found" >&2
  exit 1
fi

if [[ "${VERIFY_PDF:-0}" == "1" ]] && [[ -f /home/oai/skills/pdfs/scripts/pdf_preflight.py ]]; then
  python /home/oai/skills/pdfs/scripts/pdf_preflight.py \
    scope_ipra_framework.pdf > validation/pdf_preflight.txt
  rm -rf validation/rendered
  python /home/oai/skills/pdfs/scripts/render_pdf.py \
    scope_ipra_framework.pdf --out_dir validation/rendered --dpi 150 \
    > validation/render_log.txt
fi
