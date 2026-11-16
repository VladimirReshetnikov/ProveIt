#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd)"

cd "$ROOT/code"
python3 -m unittest -v test_native_clause_framework.py 2>&1 | tee "$ROOT/validation/python_tests.txt"
python3 demo.py 2>&1 | tee "$ROOT/validation/demo_run.txt"
python3 -m py_compile native_clause_framework.py test_native_clause_framework.py demo.py

cd "$ROOT/paper"
latexmk -pdf -interaction=nonstopmode -halt-on-error native_clause_framework.tex \
  2>&1 | tee "$ROOT/validation/latex_build.txt"
cp native_clause_framework.pdf "$ROOT/native_clause_framework.pdf"
pdfinfo native_clause_framework.pdf > "$ROOT/validation/pdfinfo.txt"
python3 /home/oai/skills/pdfs/scripts/pdf_preflight.py native_clause_framework.pdf \
  > "$ROOT/validation/pdf_preflight.txt" 2>&1

grep -E 'Overfull|Underfull|Undefined control sequence|LaTeX Warning' \
  "$ROOT/validation/latex_build.txt" > "$ROOT/validation/latex_warnings.txt" || true
latexmk -c native_clause_framework.tex >/dev/null

cd "$ROOT"
grep -RnhE '^[[:space:]]*sorry[[:space:]]*$' lean/NativeClauseFramework \
  > validation/lean_sorry_occurrences.txt || true
{
  echo "Blueprint proof-hole lines: $(wc -l < validation/lean_sorry_occurrences.txt)"
  echo "Bridge proof-hole lines: $(grep -nE '^[[:space:]]*sorry[[:space:]]*$' lean/NativeClauseFramework/Bridge.lean | wc -l)"
  echo "Axiom declarations: $(grep -RnhE '^[[:space:]]*axiom[[:space:]]' lean/NativeClauseFramework | wc -l)"
} > validation/lean_static_audit.txt

find . -type f \
  ! -name 'MANIFEST.sha256' \
  ! -path './paper/native_clause_framework.aux' \
  ! -path './paper/native_clause_framework.fdb_latexmk' \
  ! -path './paper/native_clause_framework.fls' \
  ! -path './paper/native_clause_framework.log' \
  ! -path './paper/native_clause_framework.out' \
  ! -path './paper/native_clause_framework.toc' \
  ! -path './code/__pycache__/*' \
  -print0 | sort -z | xargs -0 sha256sum > MANIFEST.sha256

echo "Built $ROOT/native_clause_framework.pdf"
