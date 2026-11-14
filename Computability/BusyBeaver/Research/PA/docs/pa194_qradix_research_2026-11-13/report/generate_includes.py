#!/usr/bin/env python3
"""Deterministically format the frozen machine and comparison data for LaTeX."""
from pathlib import Path
import json
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
def esc(s):
    return ''.join({'&':r'\&','%':r'\%','$':r'\$','#':r'\#','_':r'\_',
                    '{':r'\{','}':r'\}','~':r'\textasciitilde{}','^':r'\textasciicircum{}',
                    '\\':r'\textbackslash{}'}.get(c,c) for c in str(s))
def action(a,dense=False):
    w,d,n=a;d=('R' if d else 'L') if isinstance(d,bool) else d
    n='H' if dense and n==194 else str(n)
    return r'\texttt{'+str(w)+d+n+'}'
folds=json.loads((ROOT/'machines/PA194Q5/folds.json').read_text())
lines=[r'\begin{center}\small',r'\begin{tabular}{@{}rrrr@{}}\toprule',
       r'Deleted & Retained & New branch 0 & New branch 1\\\midrule']
for a,b,acts in folds:lines.append(f'{a} & {b} & {action(acts[0])} & {action(acts[1])}'+r'\\')
lines += [r'\bottomrule\end{tabular}',r'\end{center}',r'All labels in this fold table are native compiler labels; the delivered tables use a dense renumbering.']
(HERE/'folds.tex').write_text('\n'.join(lines)+'\n')
for k in (5,6):
    rows={}
    for line in (ROOT/f'machines/PA194Q{k}/machine.tm').read_text().splitlines():
        q,b,w,d,n=line.split();rows[int(q),int(b)]=(int(w),d,int(n))
    lines=[r'\begingroup\small\setlength{\tabcolsep}{11pt}',r'\begin{longtable}{@{}rrr@{\hspace{20pt}}rrr@{}}',
           r'\toprule State & Read 0 & Read 1 & State & Read 0 & Read 1\\\midrule\endhead',
           r'\bottomrule\endfoot']
    for q in range(97):
        z=q+97
        lines.append(f'{q} & {action(rows[q,0],True)} & {action(rows[q,1],True)} & '
                     f'{z} & {action(rows[z,0],True)} & {action(rows[z,1],True)}'+r'\\')
    lines += [r'\end{longtable}\endgroup']
    (HERE/f'table_Q{k}.tex').write_text('\n'.join(lines)+'\n')
ledger=json.loads((ROOT/'comparison/packet_ledger.json').read_text())
if isinstance(ledger,dict):ledger=ledger.get('packets',ledger.get('rows'))
assert len(ledger)==54
lines=[r'\begingroup\fontsize{8.5}{10.2}\selectfont',
       r'\begin{longtable}{@{}>{\raggedright\arraybackslash}p{0.32\linewidth}>{\raggedright\arraybackslash}p{0.64\linewidth}@{}}',
       r'\toprule Packet & Principal contribution and qualification\\\midrule\endhead',
       r'\bottomrule\endfoot']
for x in ledger:
    name=x['packet'];summary=x.get('comparison_detail',x['summary'])
    lines.append(r'\path{'+name+'}'+(' (incoming)' if x['location']=='incoming' else '')+' & '+esc(summary)+r'\\[3pt]')
lines += [r'\end{longtable}\endgroup']
(HERE/'packet_ledger.tex').write_text('\n'.join(lines)+'\n')
print('Formatted eight folds, two complete transition tables, and54 packet rows.')
