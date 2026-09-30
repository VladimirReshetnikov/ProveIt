#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")"
case "${1:-}" in
  "") ;;
  --verify) python verify.py --output verification_results.json ;;
  *) printf 'Usage: %s [--verify]\n' "$0" >&2; exit 2 ;;
esac
python make_tables.py
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
