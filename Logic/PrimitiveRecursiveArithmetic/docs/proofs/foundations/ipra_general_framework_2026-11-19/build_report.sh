#!/usr/bin/env bash
set -euo pipefail
bundle_root="$(cd -- "$(dirname -- "$0")" && pwd)"
cd -- "$bundle_root/paper"
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
