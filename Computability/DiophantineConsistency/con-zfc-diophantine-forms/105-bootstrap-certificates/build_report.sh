#!/bin/sh
set -eu
report_root=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$report_root/report"
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
