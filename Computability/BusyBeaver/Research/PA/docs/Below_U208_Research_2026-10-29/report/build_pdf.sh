#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
opts=(-interaction=nonstopmode -halt-on-error -file-line-error)
if [[ -n "${PDFLATEX_FORMAT:-}" ]]; then opts+=("-fmt=$PDFLATEX_FORMAT"); fi
"${PDFLATEX:-pdflatex}" "${opts[@]}" report.tex
"${PDFLATEX:-pdflatex}" "${opts[@]}" report.tex
