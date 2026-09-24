#!/usr/bin/env python3
"""Generate the manuscript's tables from the checked data and replayable examples."""
from pathlib import Path
import json
from construct import transition
root=Path(__file__).resolve().parents[1]
local=json.loads((root/'audit/local_check.json').read_text())
coverage=json.loads((root/'audit/coverage.json').read_text())['coverage']
lines=[]
for r in coverage:
    lines.append(f"{r['m']} & {r['labeled_antichains_visited']:,} & {r['hard_labeled_families']:,} & {r['representatives']:,} \\\\")
(root/'tables/coverage_rows.tex').write_text('\n'.join(lines)+'\n')
lines=[]
r=coverage[-1]
for n in range(4,21):
    lines.append(f"{n} & {local['by_shape'].get(f'6x{n}',0):,} & {r['by_columns'].get(str(n),0):,} \\\\")
(root/'tables/six_rows.tex').write_text('\n'.join(lines)+'\n')
r=json.loads((root/'examples/six_by_seven_certificate.json').read_text())
lines=[]
for i,j in r['T']:
    lines.append(f"$({i},{j})$ & $({r['f'][i]},{j})$ & $({i},{r['g'][j]})$ \\\\")
(root/'tables/example_images.tex').write_text('\n'.join(lines)+'\n')
w=json.loads((root/'examples/six_by_seven_word.json').read_text())
S=frozenset([(0,0)]);lines=[]
for k,a in enumerate(w['word'],1):
    S=transition(S,(a['f'],a['g']))
    f=','.join(map(str,a['f']));g=','.join(map(str,a['g']))
    lines.append(f"{k} & $({f})$ & $({g})$ & {len(S)} \\\\")
(root/'tables/example_word.tex').write_text('\n'.join(lines)+'\n')
print('Generated 4 tables from checked artifacts.')
