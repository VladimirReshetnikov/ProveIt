#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
command -v lualatex >/dev/null || { echo "LuaLaTeX is required." >&2; exit 1; }
python code/make_standalone.py
for pass in 1 2 3; do
  lualatex -interaction=nonstopmode -halt-on-error article.tex
done
if grep -Eq 'Overfull \\hbox|undefined references|multiply defined' article.log; then
  echo "Review article.log: layout or reference warnings remain." >&2
  exit 1
fi
printf '\nBuilt article.pdf. A rendered visual review is still a separate step.\n'
