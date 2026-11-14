#!/usr/bin/env python3
"""Generate the report's dense transition appendix from the literal file."""
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
table={}
for line in (ROOT/'machine/u208.tm').read_text().splitlines():
    if not line or line.startswith('#'):continue
    q,b,w,d,r=line.split();table[int(q),int(b)]=(w,d,r)
if set(table)!={(q,b) for q in range(208) for b in (0,1)}:
    raise ValueError('Incomplete dense table')
lines=[r'\begingroup\footnotesize',r'\setlength{\LTpre}{4pt}\setlength{\LTpost}{4pt}',
 r'\begin{longtable}{@{}rll@{\hspace{22mm}}rll@{}}',r'\toprule State & Read 0 & Read 1 & State & Read 0 & Read 1\\\midrule',
 r'\endfirsthead',r'\toprule State & Read 0 & Read 1 & State & Read 0 & Read 1\\\midrule',r'\endhead',
 r'\midrule\multicolumn{6}{r}{\small Continued on the next page}\\\endfoot',
 r'\bottomrule\endlastfoot']
for q in range(104):
    def action(state,b):
        w,d,r=table[state,b]
        return f'${w}\\,{d}\\,{"H" if r=="208" else r}$'
    lines.append(f'{q} & {action(q,0)} & {action(q,1)} & {q+104} & {action(q+104,0)} & {action(q+104,1)}'+r'\\')
lines.extend([r'\end{longtable}',r'\endgroup'])
(ROOT/'paper/transition_table.tex').write_text('\n'.join(lines)+'\n')
