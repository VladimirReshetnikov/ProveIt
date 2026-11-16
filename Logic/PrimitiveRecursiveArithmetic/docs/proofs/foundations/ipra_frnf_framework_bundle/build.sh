#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")" && pwd)"
VALIDATION="$ROOT/validation"
mkdir -p "$VALIDATION"

echo '[1/6] Running exact reference tests'
(
  cd "$ROOT/reference"
  python -m unittest -v test_frnf.py
) 2>&1 | tee "$VALIDATION/python_tests.txt"

echo '[2/6] Validating machine-readable metadata'
python - "$ROOT" <<'PY'
import csv
import json
import pathlib
import sys

root = pathlib.Path(sys.argv[1])
json.loads((root / 'metadata/interface.schema.json').read_text(encoding='utf-8'))
for name in ['obstacle_matrix.csv', 'theorem_ledger.csv']:
    path = root / 'metadata' / name
    with path.open(newline='', encoding='utf-8') as f:
        rows = list(csv.DictReader(f))
    if not rows:
        raise SystemExit(f'{name}: no data rows')
print('metadata JSON and CSV files parse successfully')
PY

echo '[3/6] Compiling the paper'
(
  cd "$ROOT/paper"
  pdflatex -interaction=nonstopmode -halt-on-error ipra_frnf_framework.tex >/dev/null
  pdflatex -interaction=nonstopmode -halt-on-error ipra_frnf_framework.tex >/dev/null
  pdflatex -interaction=nonstopmode -halt-on-error ipra_frnf_framework.tex >/dev/null
)

echo '[4/6] Inspecting PDF structure and text'
pdfinfo "$ROOT/paper/ipra_frnf_framework.pdf" > "$VALIDATION/pdfinfo.txt"
pdftotext "$ROOT/paper/ipra_frnf_framework.pdf" "$VALIDATION/pdftotext.txt"
test -s "$VALIDATION/pdftotext.txt"
if command -v qpdf >/dev/null 2>&1; then
  qpdf --check "$ROOT/paper/ipra_frnf_framework.pdf" \
    > "$VALIDATION/qpdf_check.txt" 2>&1
fi

echo '[5/6] Refreshing Lean source audit'
grep -RInE '\b(sorry|axiom)\b' "$ROOT/lean" \
  > "$VALIDATION/lean_placeholders.txt" || true

echo '[6/6] Removing transient TeX products'
rm -f "$ROOT/paper"/{*.aux,*.fdb_latexmk,*.fls,*.log,*.out,*.toc,*.bbl,*.blg}

echo 'Build completed successfully.'
