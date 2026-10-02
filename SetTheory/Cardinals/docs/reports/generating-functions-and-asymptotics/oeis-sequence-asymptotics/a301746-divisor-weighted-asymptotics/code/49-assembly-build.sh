#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
pdflatex -interaction=nonstopmode -halt-on-error divisor_assembly_asymptotics.tex
pdflatex -interaction=nonstopmode -halt-on-error divisor_assembly_asymptotics.tex
