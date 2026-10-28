#!/bin/sh
set -eu
report_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$report_dir"
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
