#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")"
if command -v latexmk >/dev/null 2>&1; then
  latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex
elif command -v tectonic >/dev/null 2>&1; then
  tectonic -X compile report.tex --keep-logs
else
  echo "Install a complete TeX Live distribution with latexmk, or Tectonic." >&2
  exit 1
fi
