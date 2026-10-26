#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
latexmk -xelatex -interaction=nonstopmode -halt-on-error report.tex
