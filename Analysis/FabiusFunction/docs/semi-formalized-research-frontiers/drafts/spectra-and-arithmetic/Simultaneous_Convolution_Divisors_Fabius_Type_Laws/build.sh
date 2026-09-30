#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
# ed. (2026-09-29): everything is written to build/; the recorded
# verification.json and article.pdf are never overwritten.
mkdir -p build
"${PYTHON:-python3}" verify.py --output build/verification.json
for pass in 1 2 3; do
  printf 'LaTeX pass %s/3\n' "$pass"
  if ! pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build article.tex >/dev/null; then
    tail -n 60 build/article.log >&2
    exit 1
  fi
done
if grep -Eq 'Overfull|There were undefined references|There were undefined citations' build/article.log; then
  printf 'Build completed with layout/reference warnings; inspect build/article.log.\n' >&2
  exit 1
fi
printf 'Created build/article.pdf and build/verification.json.\n'
