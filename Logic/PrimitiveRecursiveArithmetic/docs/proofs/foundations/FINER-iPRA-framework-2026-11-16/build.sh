#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")" && pwd)"
cd "$ROOT"
mkdir -p validation

printf '== Python syntax ==\n'
python3 -m compileall -q reference

printf '== Regenerate fixtures ==\n'
PYTHONPATH=reference python3 reference/generate_examples.py

printf '== Unit tests ==\n'
PYTHONPATH=reference python3 -m unittest -v reference/test_finer_reference.py \
  > validation/test_output.txt 2>&1
cat validation/test_output.txt

printf '== JSON validation ==\n'
python3 - <<'PY'
import json
from pathlib import Path
for path in sorted(Path('examples').glob('*.json')) + sorted(Path('metadata').glob('*.json')):
    json.loads(path.read_text(encoding='utf-8'))
    print(path)
PY

printf '== PDF build ==\n'
(
  cd paper
  latexmk -pdf -interaction=nonstopmode -halt-on-error finer_ipra_framework.tex
)
cp paper/finer_ipra_framework.pdf FINER-iPRA-report.pdf
cp paper/finer_ipra_framework.log validation/latex_build.log

if grep -Eq 'undefined references|LaTeX Warning: (Reference|Citation)|Overfull \\hbox' \
    validation/latex_build.log; then
  echo 'LaTeX preflight failed: unresolved reference/citation or overfull box.' >&2
  grep -E 'undefined references|LaTeX Warning: (Reference|Citation)|Overfull \\hbox' \
    validation/latex_build.log >&2 || true
  exit 1
fi

printf '== PDF metadata/fonts ==\n'
pdfinfo FINER-iPRA-report.pdf > validation/pdfinfo.txt
pdffonts FINER-iPRA-report.pdf > validation/pdffonts.txt

if [[ -x /home/oai/skills/pdfs/scripts/pdf_preflight.py || \
      -f /home/oai/skills/pdfs/scripts/pdf_preflight.py ]]; then
  python /home/oai/skills/pdfs/scripts/pdf_preflight.py FINER-iPRA-report.pdf \
    > validation/pdf_preflight.txt 2>&1
fi

printf '== Lean static status ==\n'
{
  echo 'Blueprint sorry markers:'
  grep -RIn --include='*.lean' '^[[:space:]]*sorry\b' lean/FINER || true
  echo
  echo 'Explicit axiom declarations:'
  grep -RIn --include='*.lean' '^[[:space:]]*axiom\b' lean/FINER || true
  echo
  echo 'KernelWrappers sorry count:'
  grep -c '^[[:space:]]*sorry\b' lean/FINER/KernelWrappers.lean || true
} > validation/lean_static_scan.txt
cat validation/lean_static_scan.txt

printf '== Cleanup generated intermediates ==\n'
(
  cd paper
  latexmk -c finer_ipra_framework.tex >/dev/null
)
rm -rf reference/__pycache__ validation/rendered

printf '== Checksums ==\n'
find . -type f \
  ! -path './.git/*' \
  ! -path './reference/__pycache__/*' \
  ! -name 'SHA256SUMS.txt' \
  ! -name '*.aux' ! -name '*.fdb_latexmk' ! -name '*.fls' ! -name '*.out' ! -name '*.toc' \
  -print0 | sort -z | xargs -0 sha256sum > SHA256SUMS.txt

printf 'Build complete: %s\n' "$ROOT/FINER-iPRA-report.pdf"
