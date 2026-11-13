#!/usr/bin/env bash
set -euo pipefail
task_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$task_dir"
pdflatex -interaction=nonstopmode -halt-on-error pa_flexible_output.tex
pdflatex -interaction=nonstopmode -halt-on-error pa_flexible_output.tex
pdflatex -interaction=nonstopmode -halt-on-error pa_flexible_output.tex
