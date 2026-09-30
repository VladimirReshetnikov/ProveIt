#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
"${PYTHON:-python3}" verify.py --output verification.json
for pass in 1 2 3; do
  printf 'LaTeX pass %s/3\n' "$pass"
  if ! pdflatex -interaction=nonstopmode -halt-on-error article.tex >/dev/null; then
    tail -n 60 article.log >&2
    exit 1
  fi
done
if grep -Eq 'Overfull|There were undefined references|There were undefined citations' article.log; then
  printf 'Build completed with layout/reference warnings; inspect article.log.\n' >&2
  exit 1
fi
printf 'Created article.pdf and verification.json.\n'
