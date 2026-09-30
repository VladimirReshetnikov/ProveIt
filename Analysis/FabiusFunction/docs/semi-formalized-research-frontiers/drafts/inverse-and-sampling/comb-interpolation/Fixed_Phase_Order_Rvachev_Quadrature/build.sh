#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
command -v pdflatex >/dev/null || {
  echo "pdflatex is required (install TeX Live with the packages in README.md)." >&2
  exit 1
}
# Serial passes resolve the table of contents and cross-references.
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error article.tex
done
if grep -Eq 'LaTeX Warning: (There were undefined references|Label\(s\) may have changed)' article.log; then
  echo "Unresolved cross-references; inspect article.log." >&2
  exit 1
fi
echo "Built article.pdf"
