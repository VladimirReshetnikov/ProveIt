#!/usr/bin/env sh
# Run the exact finite checks and rebuild the self-contained LaTeX article.
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
if command -v python3 >/dev/null 2>&1; then
  PYTHON=python3
elif command -v python >/dev/null 2>&1; then
  PYTHON=python
else
  printf '%s\n' 'Python 3.10 or newer is required.' >&2
  exit 1
fi
command -v pdflatex >/dev/null 2>&1 || {
  printf '%s\n' 'pdfLaTeX is required; install a LaTeX distribution.' >&2
  exit 1
}
"$PYTHON" verify.py
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error article.tex
 done
