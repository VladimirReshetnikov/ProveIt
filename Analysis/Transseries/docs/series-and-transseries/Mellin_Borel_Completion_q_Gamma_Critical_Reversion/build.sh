#!/bin/sh
set -eu
cd "$(dirname "$0")"
if ! command -v pdflatex >/dev/null 2>&1; then
  echo 'pdflatex is required; install a TeX distribution first.' >&2
  exit 1
fi
pdflatex -interaction=nonstopmode -halt-on-error critical_stokes_q_reversion.tex
pdflatex -interaction=nonstopmode -halt-on-error critical_stokes_q_reversion.tex
