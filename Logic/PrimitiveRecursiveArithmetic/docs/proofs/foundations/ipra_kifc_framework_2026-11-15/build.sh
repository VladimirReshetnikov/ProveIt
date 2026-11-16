#!/usr/bin/env sh
set -eu
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$ROOT"
python3 -m unittest -v reference/test_kifc_reference.py \
  > validation/python_tests.txt 2>&1
cd paper
pdflatex -interaction=nonstopmode -halt-on-error ipra_kifc_framework.tex \
  > ../validation/latex_pass1.log 2>&1
pdflatex -interaction=nonstopmode -halt-on-error ipra_kifc_framework.tex \
  > ../validation/latex_pass2.log 2>&1
pdflatex -interaction=nonstopmode -halt-on-error ipra_kifc_framework.tex \
  > ../validation/latex_pass3.log 2>&1
cd "$ROOT"
pdfinfo paper/ipra_kifc_framework.pdf > validation/pdfinfo.txt
if [ -f /home/oai/skills/pdfs/scripts/pdf_preflight.py ]; then
  python /home/oai/skills/pdfs/scripts/pdf_preflight.py \
    paper/ipra_kifc_framework.pdf > validation/pdf_preflight.txt 2>&1
else
  printf '%s\n' 'Preflight helper unavailable; see pdfinfo.txt.' \
    > validation/pdf_preflight.txt
fi
find . -type f ! -path './MANIFEST.sha256' ! -path './paper/*.aux' \
  ! -path './paper/*.log' ! -path './paper/*.out' ! -path './paper/*.toc' \
  -print0 | sort -z | xargs -0 sha256sum > MANIFEST.sha256
