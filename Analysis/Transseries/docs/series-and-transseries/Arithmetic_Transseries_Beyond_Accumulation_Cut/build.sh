#!/bin/sh
set -eu
cd "$(dirname "$0")"
# ProveIt edit (2026-09-29): the delivered script reran the checks in place
# and spliced the regenerated table into arithmetic_transseries.tex, which
# rewrote the authored source (with CRLF on Windows). Now the checks write
# into build/verification (ignored by git), the embedded table is only
# compared with the regenerated one, and the build stops if they differ.
# PYTHON may name the interpreter (python3 by default; use PYTHON=py on
# Windows).
PYTHON=${PYTHON:-python3}
"$PYTHON" verification/verify.py --outdir build/verification
"$PYTHON" - <<'PY'
from pathlib import Path
text = Path('arithmetic_transseries.tex').read_bytes().decode('utf-8')
start = '% BEGIN GENERATED VERIFICATION TABLE\n'
end = '% END GENERATED VERIFICATION TABLE'
if text.count(start) != 1 or text.count(end) != 1:
    raise SystemExit('Expected one pair of generated-table markers')
embedded = text.split(start, 1)[1].split(end, 1)[0]
rows = Path('build/verification/table.tex').read_bytes().decode('utf-8')
if embedded != rows:
    raise SystemExit('The regenerated table differs from the table embedded in '
                     'arithmetic_transseries.tex; compare build/verification/table.tex '
                     'and update the source deliberately.')
print('Embedded verification table matches the regenerated one.')
PY
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error arithmetic_transseries.tex
done
