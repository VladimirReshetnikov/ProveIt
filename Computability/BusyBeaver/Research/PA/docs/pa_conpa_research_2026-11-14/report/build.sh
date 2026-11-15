#!/bin/sh
set -eu
cd "$(dirname "$0")"
pdflatex -halt-on-error -interaction=nonstopmode report.tex
pdflatex -halt-on-error -interaction=nonstopmode report.tex
