#!/usr/bin/env bash
# Rebuild the report with the engine used for the delivered PDF.
set -euo pipefail

report_script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
report_bundle_dir="$(dirname -- "$report_script_dir")"

if ! command -v xelatex >/dev/null 2>&1; then
  printf '%s\n' 'XeLaTeX is required. Install a TeX distribution providing xelatex.' >&2
  exit 127
fi

cd -- "$report_bundle_dir"
for report_pass in 1 2; do
  printf 'XeLaTeX pass %s of 2\n' "$report_pass"
  xelatex -interaction=nonstopmode -halt-on-error -file-line-error report.tex
done
printf 'Report rebuilt: %s/report.pdf\n' "$report_bundle_dir"
