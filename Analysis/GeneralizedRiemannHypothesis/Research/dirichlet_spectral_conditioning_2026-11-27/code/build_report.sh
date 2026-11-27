#!/usr/bin/env bash
set -euo pipefail
report_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd -- "$report_dir"
latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error report.tex

