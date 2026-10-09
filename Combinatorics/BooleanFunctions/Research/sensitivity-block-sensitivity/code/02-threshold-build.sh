#!/usr/bin/env sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
PYTHON="${PYTHON:-python3}"
command -v "$PYTHON" >/dev/null 2>&1 || { echo "Python is required" >&2; exit 1; }
command -v pdflatex >/dev/null 2>&1 || { echo "pdfLaTeX is required" >&2; exit 1; }
"$PYTHON" code/verify_certificate.py
"$PYTHON" code/make_tables.py
mkdir -p .build
for pass in 1 2 3; do
  if ! pdflatex -interaction=nonstopmode -halt-on-error article.tex > ".build/pdflatex-$pass.log" 2>&1; then
    cat ".build/pdflatex-$pass.log" >&2
    exit 1
  fi
done
printf '\nBuilt article.pdf\n'
