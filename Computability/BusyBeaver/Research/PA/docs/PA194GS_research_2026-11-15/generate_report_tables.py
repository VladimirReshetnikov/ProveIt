#!/usr/bin/env python3
"""Generate the literal transition table and the complete 104-name ledger."""
from pathlib import Path
import csv
import json

ROOT=Path(__file__).resolve().parent
OUT=ROOT/'report/generated'
OUT.mkdir(parents=True,exist_ok=True)


def tex(s):
    replacements={'\\':r'\textbackslash{}','&':r'\&','%':r'\%',
                  '$':r'\$','#':r'\#','_':r'\_','{':r'\{','}':r'\}',
                  '~':r'\textasciitilde{}','^':r'\textasciicircum{}',
                  '→':r'$\to$','↔':r'$\leftrightarrow$','≤':r'$\le$','Γ':r'$\Gamma$'}
    return ''.join(replacements.get(c,c) for c in s)


rows={}
for line in (ROOT/'machine/machine.tm').read_text().splitlines():
    q,b,w,d,t=line.split()
    rows[int(q),int(b)]=f'{w}{d}{t}'
assert len(rows)==388
labels=json.loads((ROOT/'machine/labels.json').read_text())
table=[r'\begingroup\small\setlength{\tabcolsep}{7pt}',
       r'\begin{longtable}{rrll@{\qquad}rrll}',
       r'\caption{Complete PA194GS table. An entry $wDq$ writes $w$, moves $D$, and enters $q$. All targets in action columns are dense labels.}\label{tab:machine}\\',
       r'\toprule $q$ & Native & Read 0 & Read 1 & $q$ & Native & Read 0 & Read 1\\\midrule\endfirsthead',
       r'\toprule $q$ & Native & Read 0 & Read 1 & $q$ & Native & Read 0 & Read 1\\\midrule\endhead',
       r'\bottomrule\endfoot']
for i in range(97):
    cells=[]
    for q in (i,i+97):
        cells += [str(q),str(labels[q]),r'\texttt{'+rows[q,0]+'}',r'\texttt{'+rows[q,1]+'}']
    table.append(' & '.join(cells)+r'\\')
table += [r'\end{longtable}\endgroup']
(OUT/'machine_table.tex').write_text('\n'.join(table)+'\n')

ledger=list(csv.DictReader((ROOT/'comparison/named_designs104.csv').open()))
assert len(ledger)==104
table=[r'\begingroup\footnotesize\setlength{\tabcolsep}{4pt}\renewcommand{\arraystretch}{1.18}',
       r'\begin{longtable}{@{}>{\raggedright\arraybackslash}p{.245\textwidth}>{\raggedright\arraybackslash}p{.225\textwidth}>{\raggedright\arraybackslash}p{.48\textwidth}@{}}',
       r'\caption{All 104 named construction classes in the pinned comparison. Mechanisms and historical proof claims are attributed to their packets; this is not a list of 104 newly certified iPRA theorems. Exact graph IDs, paths and proof-status fields are in the companion CSV.}\label{tab:ledger}\\',
       r'\toprule Design & Family & Mechanism\\\midrule\endfirsthead',
       r'\toprule Design & Family & Mechanism\\\midrule\endhead',
       r'\bottomrule\endfoot']
for entry in ledger:
    name=r'\nolinkurl{'+entry['name']+'}'
    if entry['incoming_addition'].lower()=='true':
        name+=r' $\dagger$'
    table.append(name+' & '+tex(entry['family'])+' & '+tex(entry['mechanism'])+r'\\')
table += [r'\end{longtable}\endgroup',
          r'\noindent $\dagger$ A principal or supplementary construction in one of the six current incoming archives.']
(OUT/'design_ledger.tex').write_text('\n'.join(table)+'\n')

folds=json.loads((ROOT/'machine/folds.json').read_text())
table=[r'\begin{center}\begin{tabular}{rrrr}\toprule Deleted & Kept & New read 0 & New read 1\\\midrule']
for a,b,actions in folds:
    act=[str(w)+('R' if d else 'L')+str(q) for w,d,q in actions]
    table.append(f'{a} & {b} & '+r'\texttt{'+act[0]+'} & '+r'\texttt{'+act[1]+'}'+r'\\')
table += [r'\bottomrule\end{tabular}\end{center}']
(OUT/'fold_table.tex').write_text('\n'.join(table)+'\n')
print('Generated 388 transition actions, 104 design entries, and 7 contextual folds.')
