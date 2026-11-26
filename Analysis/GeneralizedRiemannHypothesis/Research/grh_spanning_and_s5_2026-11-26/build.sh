#!/bin/sh
set -eu
cd "$(dirname "$0")"
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error report.tex
