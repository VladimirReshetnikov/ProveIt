#!/bin/sh
set -eu
cd "$(dirname "$0")/article"
pdflatex -interaction=nonstopmode -halt-on-error port_registers.tex
pdflatex -interaction=nonstopmode -halt-on-error port_registers.tex
pdflatex -interaction=nonstopmode -halt-on-error port_registers.tex
