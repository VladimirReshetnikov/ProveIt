#!/usr/bin/env python3
"""Regenerate report tables from bundled evidence; Python standard library."""
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent

def tex(s):
    tr = {'\\': r'\textbackslash{}', '&': r'\&', '%': r'\%', '$': r'\$',
          '#': r'\#', '_': r'\_\allowbreak{}', '{': r'\{', '}': r'\}',
          '~': r'\textasciitilde{}', '^': r'\textasciicircum{}',
          '→': r'$\to$', '−': '$-$', '–': '--', '—': '---',
          '≤': r'$\le$', '≥': r'$\ge$', '×': r'$\times$',
          '’': "'", '“': '``', '”': "''", '`': "'"}
    return ''.join(tr.get(c, c) for c in str(s))

def write(name, text):
    (HERE / name).write_text(text + '\n')

frontier = json.loads((ROOT / 'comparison/frontier194_annotated.json').read_text())
out = [r'\small', r'\begin{longtable}{p{0.22\linewidth}p{0.58\linewidth}p{0.12\linewidth}}',
       r'\toprule Name and status & Distinguishing change & Graph prefix\\\midrule\endhead']
for r in frontier:
    role = 'reported' if r['role'] == 'reported construction' else r['role']
    out.append(tex(r['name']) + r'\newline{\footnotesize ' + tex(role) + '} & '
               + tex(r['change']) + r' & {\scriptsize\texttt{'
               + r['table_class'][:12] + r'}}\\')
out.extend([r'\bottomrule\end{longtable}', r'\normalsize'])
write('frontier_table.tex', '\n'.join(out))

ledger = json.loads((ROOT / 'comparison/packet_ledger56.json').read_text())
out = [r'\small', r'\begin{longtable}{p{0.33\linewidth}p{0.59\linewidth}}',
       r'\toprule Delivery & Contribution\\\midrule\endhead']
for r in ledger:
    out.append(r'\path{' + r['packet'] + r'}\newline{\footnotesize '
               + tex(r['location'] + '; ' + r.get('arrival','')) + '} & '
               + tex(r['summary']) + r'\\')
out.extend([r'\bottomrule\end{longtable}', r'\normalsize'])
write('packet_table.tex', '\n'.join(out))

data = [('Primary',4780,160990,267827,58154,50022512),
        ('DHS',4752,163775,274589,58014,49123904),
        ('QN',4755,161714,267227,58154,50022512),
        ('H6',4876,161158,272095,58088,49722976),
        ('HA',4750,160730,266931,58122,50022512),
        ('HAZ',4751,162682,269123,58122,50022512),
        ('SUMS',4776,160928,270059,58004,49722976),
        ('NS (sum)',4751,160711,268843,58004,49722976)]
out=[r'\begin{center}\small',r'\begin{tabular}{lrrrrr}',
     r'\toprule Input & Outcomes & Source windows & Coarse windows & Startup & Trials/template\\\midrule']
for row in data:
    out.append(row[0]+' & '+' & '.join(f'{v:,}' for v in row[1:])+r'\\')
out.extend([r'\midrule Total per template &&&&&398,382,880\\',r'\bottomrule\end{tabular}\end{center}'])
write('encoding_search_table.tex','\n'.join(out))

count_json = json.loads((ROOT/'comparison/current_census/summary.json').read_text())
counts = sorted((int(k),v) for k,v in count_json['classes_by_states'].items())
out=[r'\begin{center}\small\begin{tabular}{rrrrrr}',
     r'\toprule States & Classes & States & Classes & States & Classes\\\midrule']
for i in range(0,len(counts),3):
    row=counts[i:i+3]
    cells=[str(v) for pair in row for v in pair]
    cells += ['']*(6-len(cells))
    out.append(' & '.join(cells)+r'\\')
out.extend([r'\bottomrule\end{tabular}\end{center}'])
write('census_counts.tex','\n'.join(out))

table_path=ROOT/'machine/machine/machine.tm'
if table_path.exists():
    rows={}
    for line in table_path.read_text().splitlines():
        q,b,w,d,n=line.split();rows[int(q),int(b)]=(int(w),d,int(n))
    nstates=len(rows)//2
    assert set(q for q,b in rows)==set(range(nstates))
    write('machine_facts.tex',r'\newcommand{\prototypecount}{'+str(nstates)+'}')
    def action(q,b):
        w,d,n=rows[q,b]
        return rf'${w}\,{d}\,{n}$'
    out=[r'\small',r'\begin{longtable}{rrrrrrrr}',
         r'\toprule State & Read 0 & Read 1 && State & Read 0 & Read 1 &\\\midrule\endhead']
    half=(nstates+1)//2
    for q in range(half):
        r=q+half
        row=f'{q} & {action(q,0)} & {action(q,1)} &'
        if r<nstates:row+=f' & {r} & {action(r,0)} & {action(r,1)} &'
        else:row+=' & & & &'
        out.append(row+r'\\')
    out.extend([r'\bottomrule\end{longtable}',r'\normalsize'])
    write('transition_table.tex','\n'.join(out))
print('Generated report tables from the bundled records.')
