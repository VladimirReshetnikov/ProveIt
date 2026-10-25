#!/usr/bin/env bash
set -euo pipefail
artifact_root="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
python3 -B "$artifact_root/code/report_inputs.py"
cd "$artifact_root/report"
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
