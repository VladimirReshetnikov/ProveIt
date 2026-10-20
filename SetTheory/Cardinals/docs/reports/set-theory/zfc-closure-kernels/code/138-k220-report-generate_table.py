#!/usr/bin/env python3
"""Generate the entire canonical transition table for the TeX appendix."""
from pathlib import Path
import hashlib
HERE=Path(__file__).resolve().parent
raw=(HERE.parent/'machine/k220.tm').read_bytes()
assert hashlib.sha256(raw).hexdigest()=='f80c57e800d4f999d9b4902a8e96bd36d1b6180b3ad322ca8ed0ab67b47f2a5f'
rows={}
for line in raw.decode().splitlines():
    if not line or line.startswith('#'):continue
    q,b,w,d,z=line.split();rows[int(q),int(b)]=w+d+z
assert set(rows)=={(q,b)for q in range(220)for b in(0,1)}
heading=' & '.join([r'\normalfont State & \normalfont Read 0 & \normalfont Read 1']*3)+r'\\'
lines=[r'\begingroup',r'\small\ttfamily',r'\setlength{\tabcolsep}{5pt}',
       r'\begin{longtable}{rrr@{\hspace{7mm}}rrr@{\hspace{7mm}}rrr}',r'\toprule',
       heading,
       r'\midrule\endfirsthead',r'\toprule',
       heading,
       r'\midrule\endhead',r'\midrule\endfoot',r'\bottomrule\endlastfoot']
for q in range(74):
    fields=[]
    for z in (q,q+74,q+148):
        fields.extend([str(z),rows[z,0],rows[z,1]] if z<220 else ['','',''])
    lines.append(' & '.join(fields)+r'\\')
lines.extend([r'\end{longtable}',r'\endgroup'])
(HERE/'transition_table.tex').write_text('\n'.join(lines)+'\n')
