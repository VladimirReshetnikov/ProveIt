#!/usr/bin/env bash
set -euo pipefail
report_root="$(cd "$(dirname "$0")/.." && pwd)"
build_root="$(mktemp -d)"
trap 'rm -rf "$build_root"' EXIT
cd "$report_root"
xelatex -interaction=nonstopmode -halt-on-error -output-directory "$build_root" report.tex
xelatex -interaction=nonstopmode -halt-on-error -output-directory "$build_root" report.tex
xelatex -interaction=nonstopmode -halt-on-error -output-directory "$build_root" report.tex
cp "$build_root/report.pdf" "$report_root/report.pdf"
