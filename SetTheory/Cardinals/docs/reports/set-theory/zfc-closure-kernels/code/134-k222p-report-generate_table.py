#!/usr/bin/env python3
"""Generate the complete LaTeX table from the pinned canonical 222 machine."""
from pathlib import Path
import hashlib

ROOT = Path(__file__).resolve().parent
table_path = ROOT.parent / 'portable/machine/candidate222.tm'
raw = table_path.read_bytes()
assert hashlib.sha256(raw).hexdigest() == '3bcf4678c9c576ae99a108c32038f035b42204289267d05a34ba2b37b32b6476'
rows = {}
for line in raw.decode().splitlines():
    if not line or line.startswith('#'):
        continue
    q, b, w, d, z = line.split()
    rows[int(q), int(b)] = (int(w), d, int(z))
assert set(rows) == {(q,b) for q in range(222) for b in (0,1)}
lines = [r'{\small\setlength{\tabcolsep}{5pt}',
         r'\begin{longtable}{rcc@{\qquad}rcc@{\qquad}rcc}',
         r'\toprule',
         r'$q$ & 0 & 1 & $q$ & 0 & 1 & $q$ & 0 & 1\\',
         r'\midrule\endfirsthead',
         r'\toprule',
         r'$q$ & 0 & 1 & $q$ & 0 & 1 & $q$ & 0 & 1\\',
         r'\midrule\endhead',
         r'\midrule\multicolumn{9}{r}{Continued on the next page}\\\endfoot',
         r'\bottomrule\endlastfoot']
for i in range(74):
    fields = []
    for q in (i, i+74, i+148):
        fields.append(str(q))
        for b in (0, 1):
            w,d,z = rows[q,b]
            fields.append(f'$({w},{d},{z})$')
    lines.append(' & '.join(fields) + r'\\')
lines += [r'\end{longtable}', '}']
(ROOT/'transition_table.tex').write_text('\n'.join(lines)+'\n')
print('Generated all 444 transitions in 222 state entries.')
