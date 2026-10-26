#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")/.."
xelatex -interaction=nonstopmode -halt-on-error report.tex
xelatex -interaction=nonstopmode -halt-on-error report.tex
