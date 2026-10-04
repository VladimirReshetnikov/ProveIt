#!/usr/bin/env bash
# Rebuild from any working directory; TeX intermediate files stay temporary.
set -euo pipefail
HERE="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
command -v python3 >/dev/null || { echo 'python3 is required' >&2; exit 1; }
command -v pdflatex >/dev/null || { echo 'pdflatex is required' >&2; exit 1; }
python3 "$HERE/verify.py"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
cd "$HERE"
for pass in 1 2 3; do
  if ! pdflatex -interaction=nonstopmode -halt-on-error \
      -output-directory="$WORK" "$HERE/article.tex" >"$WORK/pass-$pass.log" 2>&1; then
    cat "$WORK/pass-$pass.log" >&2
    exit 1
  fi
done
cp "$WORK/article.pdf" "$HERE/article.pdf"
if grep -E 'Overfull|undefined|multiply defined' "$WORK/pass-3.log"; then
  echo 'Review the TeX warnings above.' >&2
fi
printf '\nBuilt %s\n' "$HERE/article.pdf"
