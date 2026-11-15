#!/usr/bin/env python3
"""Generate the printed transition table directly from the delivered bytes."""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
rows = {}
for line in (ROOT / 'machines/PA194ORH/machine.tm').read_text().splitlines():
    q, b, w, d, n = line.split()
    rows[int(q), int(b)] = f'{w}{d}{n}'
assert set(rows) == {(q,b) for q in range(194) for b in (0,1)}
out = [r'\begingroup', r'\small', r'\setlength{\tabcolsep}{12pt}',
       r'\begin{longtable}{rllrll}',
       r'\toprule State & Read 0 & Read 1 & State & Read 0 & Read 1 \\',
       r'\midrule\endfirsthead',
       r'\toprule State & Read 0 & Read 1 & State & Read 0 & Read 1 \\',
       r'\midrule\endhead', r'\midrule\multicolumn{6}{r}{Continued on the next page}\\\endfoot',
       r'\bottomrule\endlastfoot']
for a in range(97):
    b = a + 97
    out.append(f'{a} & \\texttt{{{rows[a,0]}}} & \\texttt{{{rows[a,1]}}} & '
               f'{b} & \\texttt{{{rows[b,0]}}} & \\texttt{{{rows[b,1]}}} \\\\')
out += [r'\end{longtable}', r'\endgroup']
(ROOT / 'report/transition_table.tex').write_text('\n'.join(out)+'\n')
print('Generated 194 states / 388 printed transitions.')
