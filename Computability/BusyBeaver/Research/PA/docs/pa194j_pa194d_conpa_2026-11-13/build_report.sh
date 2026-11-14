#!/usr/bin/env bash
set -euo pipefail
report_root=$(CDPATH= cd -- "$(dirname -- "$0")/report" && pwd)
cd "$report_root"
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error pa194j_conpa.tex
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error pa194j_conpa.tex
