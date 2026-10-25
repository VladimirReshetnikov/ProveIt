#!/usr/bin/env sh
set -eu
packet_root=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$packet_root"
python3 -B code/report_inputs.py --check
pdflatex -interaction=nonstopmode -halt-on-error ConZFC_Fixed_Base_Modular.tex
pdflatex -interaction=nonstopmode -halt-on-error ConZFC_Fixed_Base_Modular.tex
