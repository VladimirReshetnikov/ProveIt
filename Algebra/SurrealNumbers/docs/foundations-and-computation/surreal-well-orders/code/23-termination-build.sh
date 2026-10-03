#!/bin/sh
# Compile the self-contained article. No shell escape or network access needed.
set -eu
cd "$(dirname "$0")"
command -v pdflatex >/dev/null 2>&1 || {
  echo "pdflatex is required (TeX Live or MiKTeX)." >&2
  exit 1
}
for pass in 1 2 3; do
  if ! pdflatex -interaction=nonstopmode -halt-on-error article.tex > build.log; then
    tail -50 build.log >&2
    exit 1
  fi
done
if grep -Eq 'undefined references|undefined citations|multiply defined|Overfull|destination with the same identifier' article.log; then
  echo "LaTeX preflight failed; inspect article.log." >&2
  exit 1
fi
printf 'Built article.pdf\n'
