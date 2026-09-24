#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
PYTHON="${PYTHON:-python3}"
TEX_ENGINE="${TEX_ENGINE:-pdflatex}"
command -v "$PYTHON" >/dev/null || { echo "Python executable not found: $PYTHON" >&2; exit 1; }
command -v "$TEX_ENGINE" >/dev/null || { echo "LaTeX executable not found: $TEX_ENGINE" >&2; exit 1; }
"$PYTHON" verify.py | tee verification-output.txt
"$TEX_ENGINE" -interaction=nonstopmode -halt-on-error article.tex
"$TEX_ENGINE" -interaction=nonstopmode -halt-on-error article.tex
