#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
mkdir -p "$ROOT/validation"

{
  echo "# Python reference validation"
  echo "date_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "python=$(python3 --version 2>&1)"
  echo
  PYTHONPATH="$ROOT/reference" python3 -m unittest -v \
    "$ROOT/reference/test_fqnf_reference.py"
} > "$ROOT/validation/python_tests.txt" 2>&1

python3 -m py_compile \
  "$ROOT/reference/fqnf_reference.py" \
  "$ROOT/reference/test_fqnf_reference.py"

python3 - <<'PY' "$ROOT"
import json
from pathlib import Path
import sys
root = Path(sys.argv[1])
for path in sorted((root / "examples").glob("*.json")):
    json.loads(path.read_text())
print("JSON examples: valid")
PY

(
  cd "$ROOT/paper"
  latexmk -pdf -interaction=nonstopmode -halt-on-error fqnf_ipra.tex
) > "$ROOT/validation/latex_build.log" 2>&1

pdfinfo "$ROOT/paper/fqnf_ipra.pdf" > "$ROOT/validation/pdfinfo.txt"

{
  echo "# Lean static audit"
  echo "Lean executable: $(command -v lean || echo unavailable)"
  echo "Lake executable: $(command -v lake || echo unavailable)"
  echo
  echo "KernelCore placeholders:"
  grep -nE '^[[:space:]]*(sorry|admit|axiom)([[:space:]]|$)' "$ROOT/lean/FQNF/KernelCore.lean" || true
  echo
  echo "All visible roadmap placeholders:"
  grep -R -nE '^[[:space:]]*(sorry|admit|axiom)([[:space:]]|$)' "$ROOT/lean/FQNF" || true
} > "$ROOT/validation/lean_static_audit.txt"

if grep -qE 'Overfull|Undefined control|LaTeX Warning: Reference|Citation.*undefined|Fatal error' \
  "$ROOT/validation/latex_build.log"; then
  echo "LaTeX validation found a layout or reference error." >&2
  exit 1
fi

(
  cd "$ROOT"
  find . -type f \
    ! -name 'MANIFEST.sha256' \
    ! -path './paper/*.aux' \
    ! -path './paper/*.fdb_latexmk' \
    ! -path './paper/*.fls' \
    ! -path './paper/*.log' \
    ! -path './paper/*.out' \
    ! -path './paper/*.toc' \
    ! -path '*/__pycache__/*' \
    -print0 | sort -z | xargs -0 sha256sum
) > "$ROOT/MANIFEST.sha256"

echo "Build and validation completed."
