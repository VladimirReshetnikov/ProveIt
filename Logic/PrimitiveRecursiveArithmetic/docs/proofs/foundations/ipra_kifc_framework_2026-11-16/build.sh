#!/usr/bin/env sh
set -eu
export PYTHONDONTWRITEBYTECODE=1

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$ROOT"
mkdir -p validation

python3 -m unittest discover -s reference -p 'test_*.py' -v \
  > validation/python_tests.txt 2>&1

python3 - <<'PY' > validation/json_validation.txt
import csv
import json
import re
from pathlib import Path

import jsonschema

root = Path('.')
schema = json.loads((root / 'metadata/framework_schema.json').read_text())

for path in sorted((root / 'examples').glob('*_graph.json')):
    data = json.loads(path.read_text())
    jsonschema.Draft202012Validator(schema).validate(data)
    print(f'VALID {path}')

for path in sorted((root / 'examples').glob('*.json')):
    json.loads(path.read_text())
    print(f'PARSED {path}')

json.loads((root / 'metadata/proof_status.json').read_text())
print('PARSED metadata/proof_status.json')

for path in sorted((root / 'metadata').glob('*.csv')):
    rows = list(csv.reader(path.open(newline='')))
    width = len(rows[0])
    assert all(len(row) == width for row in rows), path
    print(f'CSV {path}: {len(rows) - 1} data rows, {width} columns')

report = (root / 'paper/sections/16_status.tex').read_text()
ledger = (root / 'metadata/THEOREM_LEDGER.md').read_text()
for prefix, count in [('K', 24), ('B', 5)]:
    expected = {f'{prefix}{i}' for i in range(1, count + 1)}
    report_ids = set(re.findall(rf'(?m)^({prefix}\d+)\s*&', report))
    ledger_ids = set(re.findall(rf'(?m)^\| ({prefix}\d+) \|', ledger))
    assert report_ids == expected, ('report', prefix, report_ids ^ expected)
    assert ledger_ids == expected, ('ledger', prefix, ledger_ids ^ expected)
print('Theorem ledger IDs agree: K1-K24 and B1-B5.')
print('All JSON files parse; graph examples satisfy the schema.')
PY

{
  printf 'lean: '; command -v lean || printf 'unavailable\n'
  printf 'lake: '; command -v lake || printf 'unavailable\n'
  printf '\nExplicit proof placeholders in Lean sources:\n'
  grep -RInE '(^[[:space:]]*sorry$|=> sorry$|all_goals sorry$)' lean || true
  printf '\nDeclared axioms in supplied Lean sources (should print no matches):\n'
  grep -RInE '^[[:space:]]*axiom ' lean || true
  printf '\nNon-retained-transfer source scan (should print no matches):\n'
  find lean -type f -name '*.lean' \
    ! -name 'RetainedTransferBlueprint.lean' -print0 \
    | xargs -0 grep -nE \
      '(^[[:space:]]*sorry$|=> sorry$|all_goals sorry$|^[[:space:]]*axiom )' \
    || true
} > validation/lean_source_scan.txt

cd paper
latexmk -pdf -interaction=nonstopmode -halt-on-error ipra_kifc_framework.tex \
  > ../validation/latexmk.log 2>&1
cd "$ROOT"

pdfinfo paper/ipra_kifc_framework.pdf > validation/pdfinfo.txt
python /home/oai/skills/pdfs/scripts/pdf_inspect.py \
  paper/ipra_kifc_framework.pdf > validation/pdf_inspect.txt 2>&1
python /home/oai/skills/pdfs/scripts/pdf_preflight.py \
  paper/ipra_kifc_framework.pdf > validation/pdf_preflight.txt 2>&1

rm -rf reference/__pycache__

find . -type f ! -path './MANIFEST.sha256' \
  ! -path './paper/*.aux' ! -path './paper/*.log' \
  ! -path './paper/*.out' ! -path './paper/*.toc' \
  ! -path './paper/*.fls' ! -path './paper/*.fdb_latexmk' \
  -print0 | sort -z | xargs -0 sha256sum > MANIFEST.sha256
