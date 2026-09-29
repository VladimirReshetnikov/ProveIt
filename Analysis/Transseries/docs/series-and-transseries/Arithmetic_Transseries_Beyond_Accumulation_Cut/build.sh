#!/bin/sh
set -eu
cd "$(dirname "$0")"
python3 verification/verify.py
python3 - <<'PY'
from pathlib import Path
source = Path('arithmetic_transseries.tex')
text = source.read_text()
start = '% BEGIN GENERATED VERIFICATION TABLE\n'
end = '% END GENERATED VERIFICATION TABLE'
if text.count(start) != 1 or text.count(end) != 1:
    raise RuntimeError('Expected one pair of generated-table markers')
head, tail = text.split(start, 1)
_, tail = tail.split(end, 1)
rows = Path('verification/table.tex').read_text()
source.write_text(head + start + rows + end + tail)
PY
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error arithmetic_transseries.tex
done
