#!/usr/bin/env python3
"""Regenerate the report's complete transition table from the dense DR215 file."""
from pathlib import Path

ROOT=Path(__file__).resolve().parent
table={}
for line in (ROOT.parent/'DR215/machine/dr215.tm').read_text().splitlines():
    if not line or line.startswith('#'):
        continue
    q,b,w,d,z=line.split()
    assert (int(q),int(b)) not in table and d in ('L','R')
    table[int(q),int(b)]=w+d+z
assert set(table)=={(q,b) for q in range(215) for b in (0,1)}
header=' & '.join(['$q$','$0$','$1$']*4)+r'\\'
lines=[r'\begingroup\fontsize{8.5}{10}\selectfont\ttfamily',
       r'\setlength{\tabcolsep}{4pt}',
       r'\begin{longtable}{rll@{\hspace{1em}}rll@{\hspace{1em}}rll@{\hspace{1em}}rll}',
       r'\toprule',header,r'\midrule',r'\endfirsthead',
       r'\toprule',header,r'\midrule',r'\endhead',
       r'\midrule',r'\multicolumn{12}{r}{\normalfont\footnotesize Continued on next page}\\',
       r'\endfoot',r'\bottomrule',r'\endlastfoot']
for i in range(54):
    cells=[]
    for q in (i,i+54,i+108,i+162):
        cells.extend([str(q),table[q,0],table[q,1]] if q<215 else ['','',''])
    lines.append(' & '.join(cells)+r'\\')
lines.extend([r'\end{longtable}',r'\endgroup'])
(ROOT/'machine_table.tex').write_text('\n'.join(lines)+'\n')
print('Generated all 430 transition rows for 215 working states.')
