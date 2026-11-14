#!/usr/bin/env python3
"""Generate report tables from the delivered machine and comparison data."""
from pathlib import Path
import csv
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent

def esc(s):
    return ''.join({'\\':r'\textbackslash{}','&':r'\&','%':r'\%','$':r'\$','#':r'\#','_':r'\_','{':r'\{','}':r'\}','~':r'\textasciitilde{}','^':r'\textasciicircum{}'}.get(c,c) for c in str(s))
rows={}
for l in (ROOT/'machine/machine.tm').read_text().splitlines():
    if not l.strip() or l.startswith('#'):continue
    q,b,w,d,n=l.split();rows[int(q),int(b)]=(w,d,'H' if n=='194' else n)
def act(q,b):
    w,d,n=rows[q,b];return '$'+w+d+n+'$'
lines=[r'\begin{longtable}{rll@{\hspace{1.6cm}}rll}',r'\toprule State & Read 0 & Read 1 & State & Read 0 & Read 1\\\midrule',r'\endhead']
for q in range(97):
    k=q+97
    lines.append(f'{q}&{act(q,0)}&{act(q,1)}&{k}&{act(k,0)}&{act(k,1)}'+r'\\')
lines.extend([r'\bottomrule',r'\end{longtable}'])
(HERE/'transition_table.tex').write_text('\n'.join(lines)+'\n')
a=list(csv.DictReader((ROOT/'comparison/frontier194.csv').open()))
lines=[r'{\small',r'\begin{longtable}{p{0.21\textwidth}p{0.14\textwidth}p{0.54\textwidth}}',r'\toprule Name and short hash & Status & Distinction\\\midrule\endhead']
for x in a:
    status='Rejected' if x['status']=='rejected' else ('Auxiliary' if x['status'].startswith('auxiliary') else 'Reported')
    lines.append(esc(x['name'])+r'\newline{\ttfamily '+x['representative_sha256'][:12]+'}&'+status+'&'+esc(x['change'])+r'\\[3pt]')
lines.extend([r'\bottomrule\end{longtable}',r'}'])
(HERE/'frontier194.tex').write_text('\n'.join(lines)+'\n')
a=list(csv.DictReader((ROOT/'comparison/packet_ledger.csv').open()))
lines=[r'{\small',r'\begin{longtable}{rp{0.37\textwidth}p{0.51\textwidth}}',r'\toprule No. & Packet & Contribution or status\\\midrule\endhead']
for i,x in enumerate(a,1):
    lines.append(str(i)+r'&\nolinkurl{'+x['packet']+'}&'+esc(x['contribution'].replace('`',''))+r'\\[3pt]')
lines.extend([r'\bottomrule\end{longtable}',r'}'])
(HERE/'packet_ledger.tex').write_text('\n'.join(lines)+'\n')
print('Generated full table,34-class frontier and',len(a),'packet ledger.')
