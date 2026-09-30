#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")"
# ed. (2026-09-29): the tables are regenerated only with --tables (make_tables.py rewrites the
# filed table inputs), and --verify writes build/rerun_results.json instead of the recorded JSON.
case "${1:-}" in
  "") ;;
  --verify) "${PYTHON:-python}" verify.py ;;
  --tables) "${PYTHON:-python}" make_tables.py ;;
  *) printf 'Usage: %s [--verify|--tables]\n' "$0" >&2; exit 2 ;;
esac
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
