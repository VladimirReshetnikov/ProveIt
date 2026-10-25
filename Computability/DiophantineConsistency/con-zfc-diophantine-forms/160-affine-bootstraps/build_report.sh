#!/bin/sh
set -eu
cd "$(dirname "$0")"
python3 -B code/report_inputs.py --check
cd report
pdflatex -interaction=nonstopmode -halt-on-error main.tex > build_pass1.txt
pdflatex -interaction=nonstopmode -halt-on-error main.tex > build_pass2.txt
pdflatex -interaction=nonstopmode -halt-on-error main.tex > build_pass3.txt
python3 - <<'PY'
from pathlib import Path
import shutil
log=Path('main.log').read_text()
bad=[line for line in log.splitlines() if 'Overfull' in line or 'undefined' in line or 'Rerun to get' in line]
if bad:
    raise SystemExit('\n'.join(bad))
shutil.copyfile('main.pdf','../ConZFC_Affine_Bootstraps.pdf')
print('Compiled report; no overfull boxes or unresolved references.')
PY
