#!/usr/bin/env bash
set -euo pipefail
ROOT=$(cd "$(dirname "$0")" && pwd)
cd "$ROOT"
mkdir -p validation

(cd code && python3 -m unittest -v test_conway_core.py) 2>&1 | tee validation/python_tests.txt
python3 code/conway_core.py examples/zigzag_conway_tile.json \
  --output examples/zigzag_conway_tile_report.json
python3 figures/make_figures.py 2>&1 | tee validation/figure_build.txt

(
  cd paper
  latexmk -pdf -interaction=nonstopmode -halt-on-error conway_criterion_ipra.tex
) 2>&1 | tee validation/latex_build.txt

python3 - <<'PY'
from pathlib import Path
import hashlib
root = Path('.')
items=[]
for p in sorted(root.rglob('*')):
    if not p.is_file():
        continue
    if p.name == 'MANIFEST.sha256' or any(part in {'.git','__pycache__'} for part in p.parts):
        continue
    if p.suffix in {'.aux','.fdb_latexmk','.fls','.log','.out','.toc'}:
        continue
    h=hashlib.sha256(p.read_bytes()).hexdigest()
    items.append(f"{h}  {p.as_posix()}")
(root/'MANIFEST.sha256').write_text('\n'.join(items)+'\n', encoding='utf-8')
PY
