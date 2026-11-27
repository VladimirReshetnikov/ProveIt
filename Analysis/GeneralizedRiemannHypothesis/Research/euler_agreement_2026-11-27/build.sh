#!/bin/sh
set -eu
cd "$(dirname "$0")"
if command -v tectonic >/dev/null 2>&1; then
    tectonic sharp_euler_agreement.tex
elif command -v pdflatex >/dev/null 2>&1; then
    pdflatex -interaction=nonstopmode -halt-on-error sharp_euler_agreement.tex
    pdflatex -interaction=nonstopmode -halt-on-error sharp_euler_agreement.tex
else
    echo 'Install Tectonic or a working TeX Live/MiKTeX distribution to rebuild.' >&2
    exit 1
fi
