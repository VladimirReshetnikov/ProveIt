#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
pdflatex -halt-on-error -interaction=nonstopmode Euler_Group_Terminals.tex
bibtex Euler_Group_Terminals
pdflatex -halt-on-error -interaction=nonstopmode Euler_Group_Terminals.tex
pdflatex -halt-on-error -interaction=nonstopmode Euler_Group_Terminals.tex
