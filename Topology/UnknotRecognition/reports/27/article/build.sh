#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
# A fixed epoch makes pdfTeX metadata reproducible across rebuilds.
export SOURCE_DATE_EPOCH="${SOURCE_DATE_EPOCH:-1791374400}"
export FORCE_SOURCE_DATE=1
export TZ=UTC
for _ in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error report25.tex
done
