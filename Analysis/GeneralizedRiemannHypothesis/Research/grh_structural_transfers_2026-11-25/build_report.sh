#!/bin/sh
set -eu
cd "$(dirname "$0")"
case "${REPORT_TEX_ENGINE:-pdflatex}" in
  pdflatex)
    pdflatex -interaction=nonstopmode -halt-on-error report.tex
    pdflatex -interaction=nonstopmode -halt-on-error report.tex
    pdflatex -interaction=nonstopmode -halt-on-error report.tex
    ;;
  tectonic)
    tectonic --keep-logs report.tex
    ;;
  *)
    printf '%s\n' 'Set REPORT_TEX_ENGINE to pdflatex or tectonic.' >&2
    exit 2
    ;;
esac
