#!/usr/bin/env bash
set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
ROOT="$(cd "$(dirname "$0")" && pwd)"
cd "$ROOT"

mkdir -p validation
rm -f MANIFEST.sha256
python3 verify.py | tee validation/verify.log

if command -v pdflatex >/dev/null 2>&1; then
  (
    cd paper
    pdflatex -interaction=nonstopmode -halt-on-error ipra_staged_contract_kernel.tex
    pdflatex -interaction=nonstopmode -halt-on-error ipra_staged_contract_kernel.tex
    pdflatex -interaction=nonstopmode -halt-on-error ipra_staged_contract_kernel.tex
  ) | tee validation/pdflatex.log
else
  echo "pdflatex unavailable; retaining any existing PDF" | tee validation/pdflatex.log
fi

if command -v pdfinfo >/dev/null 2>&1 && [[ -f paper/ipra_staged_contract_kernel.pdf ]]; then
  pdfinfo paper/ipra_staged_contract_kernel.pdf > validation/pdfinfo.txt
fi

rm -f paper/*.aux paper/*.log paper/*.out paper/*.toc paper/*.fls paper/*.fdb_latexmk
rm -rf __pycache__ code/__pycache__

find . -type f \
  ! -path './MANIFEST.sha256' \
  ! -path './validation/manifest_check.log' \
  -print0 | sort -z | xargs -0 sha256sum > MANIFEST.sha256

python3 verify.py | tee validation/manifest_check.log

echo "Build complete."
