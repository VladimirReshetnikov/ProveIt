#!/bin/sh
# Build the standalone article. Optional --check preserves the delivered JSON.
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
case "${1-}" in
  "") ;;
  --check)
    command -v python3 >/dev/null 2>&1 || {
      echo 'Python 3.10 or newer is required for --check.' >&2; exit 1;
    }
    python3 verify_examples.py --output verification.recheck.json
    ;;
  *) echo 'Usage: sh build.sh [--check]' >&2; exit 2 ;;
esac
command -v latexmk >/dev/null 2>&1 || {
  echo 'latexmk and a LaTeX distribution are required.' >&2; exit 1;
}
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
