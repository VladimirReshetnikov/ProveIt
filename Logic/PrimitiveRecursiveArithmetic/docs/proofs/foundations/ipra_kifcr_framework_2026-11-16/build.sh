#!/usr/bin/env sh
set -eu

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$ROOT"
mkdir -p validation

python3 -m py_compile \
  reference/kifcr_reference.py reference/test_kifcr_reference.py \
  > validation/python_compile.txt 2>&1
printf '%s\n' 'PASS: Python sources compile.' >> validation/python_compile.txt

python3 -m unittest -v reference/test_kifcr_reference.py \
  > validation/python_tests.txt 2>&1

python3 - <<'PY' > validation/json_validation.txt 2>&1
import json
from pathlib import Path
root = Path('.')
paths = sorted(root.rglob('*.json'))
for p in paths:
    json.loads(p.read_text())
    print('PASS', p)
print(f'PASS: {len(paths)} JSON files parsed.')
PY

{
  echo '$ source scan for admitted Lean declarations'
  if grep -RInE '^[[:space:]]*(axiom|sorry)[[:space:]]' lean --include='*.lean'; then
    echo 'FAIL: found axiom or sorry declaration.'
    exit 1
  else
    echo 'PASS: no Lean axiom or sorry declarations.'
  fi
  if grep -RInE '\badmit\b' lean --include='*.lean'; then
    echo 'FAIL: found admit placeholder.'
    exit 1
  else
    echo 'PASS: no admit placeholder.'
  fi
  printf 'Lean files: '
  find lean -name '*.lean' -type f | wc -l
  echo 'NOTE: this source scan is not a Lean build.'
} > validation/lean_source_scan.txt 2>&1

cd paper
pdflatex -interaction=nonstopmode -halt-on-error ipra_kifcr_framework.tex \
  > ../validation/latex_pass1.log 2>&1
pdflatex -interaction=nonstopmode -halt-on-error ipra_kifcr_framework.tex \
  > ../validation/latex_pass2.log 2>&1
pdflatex -interaction=nonstopmode -halt-on-error ipra_kifcr_framework.tex \
  > ../validation/latex_pass3.log 2>&1
cd "$ROOT"

pdfinfo paper/ipra_kifcr_framework.pdf > validation/pdfinfo.txt
pdftotext -layout paper/ipra_kifcr_framework.pdf validation/pdf_text.txt
pdffonts paper/ipra_kifcr_framework.pdf > validation/pdf_fonts.txt

if [ -f /home/oai/skills/pdfs/scripts/pdf_preflight.py ]; then
  python /home/oai/skills/pdfs/scripts/pdf_preflight.py \
    paper/ipra_kifcr_framework.pdf > validation/pdf_preflight.txt 2>&1
else
  printf '%s\n' 'Preflight helper unavailable; see pdfinfo.txt.' \
    > validation/pdf_preflight.txt
fi

{
  echo '$ PDF static diagnostics'
  pdfinfo paper/ipra_kifcr_framework.pdf | grep '^Pages:'
  if grep -En 'undefined references|LaTeX Warning: Reference .* undefined|Citation .* undefined|^! |Overfull \\hbox|Overfull \\vbox' validation/latex_pass3.log; then
    echo 'FAIL: final LaTeX log contains a blocking diagnostic.'
    exit 1
  else
    echo 'PASS: no unresolved references, TeX errors, or overfull boxes.'
  fi
  test -s validation/pdf_text.txt
  echo 'PASS: pdftotext produced nonempty text.'
} > validation/artifact_checks.txt 2>&1

rm -rf reference/__pycache__
find . -type f \
  ! -path './MANIFEST.sha256' \
  ! -path './paper/*.aux' \
  ! -path './paper/*.log' \
  ! -path './paper/*.out' \
  ! -path './paper/*.toc' \
  ! -path './*/__pycache__/*' \
  ! -name '*.pyc' \
  -print0 | sort -z | xargs -0 sha256sum > MANIFEST.sha256
