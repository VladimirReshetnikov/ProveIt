#!/usr/bin/env sh
set -eu
artifact_dir=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$artifact_dir/report"
latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex
