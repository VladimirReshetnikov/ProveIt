#!/bin/sh
set -eu
cd "$(dirname "$0")"
python3 verify_examples.py
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error \
    glazer_presburger_embeddings.tex > "build-pass-${pass}.log"
done
python3 - <<'PY'
from pathlib import Path
log = Path('glazer_presburger_embeddings.log').read_text()
bad = ['undefined references', 'undefined citations', 'Overfull \\hbox',
       'Overfull \\vbox', 'multiply defined', 'Token not allowed in a PDF string']
found = [item for item in bad if item in log]
if found:
    raise SystemExit('Build issues requiring inspection: ' + ', '.join(found))
print('PDF built with resolved references and no overfull boxes.')
PY
