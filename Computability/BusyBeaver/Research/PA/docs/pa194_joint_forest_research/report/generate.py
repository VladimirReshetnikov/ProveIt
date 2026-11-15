#!/usr/bin/env python3
"""Generate all numerical tables directly from the released artifacts."""
from pathlib import Path
import csv,json,hashlib
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
NAMES=('PA194ForestR','PA194ForestB','PA194ForestX')

def esc(text):
    mapping={'&':r'\&','%':r'\%','$':r'\$','#':r'\#','_':r'\_',
             '{':r'\{','}':r'\}','~':r'\textasciitilde{}','^':r'\textasciicircum{}',
             '\\':r'\textbackslash{}'}
    s=''.join(mapping.get(x,x) for x in str(text))
    for a,b in {'Γ':r'\(\Gamma\)','→':r'\(\to\)','−':'-',
                '≤':r'\(\le\)','Σ':r'\(\Sigma\)','σ':r'\(\sigma\)','₁':'1',
                '↔':r'\(\leftrightarrow\)','–':'-','—':'--',
                '’':"'",'“':'``','”':"''"}.items():s=s.replace(a,b)
    return s

lines=[r'\begin{center}',r'\small',
       r'\begin{tabular}{lrrrrr}',r'\toprule',
       r'Machine & Fixed & AX readers & Folds & Changed addresses & Startup\\\midrule']
for name in NAMES:
    d=ROOT/'machines'/name
    r=json.loads((d/'receipt.json').read_text())
    lines.append(f"{name} & {r['fixed_states']} & {r['reader_states']} & {r['folds']} & {r['changed_addresses']} & {r['startup']['steps']:,} "+r'\\')
lines += [r'\bottomrule',r'\end{tabular}',r'\end{center}',
          'The count is fixed controls plus AX reader controls minus simultaneous folds. Each result is 194.',
          r'\begin{center}\small',r'\begin{tabular}{lrr}',r'\toprule',
          r'Machine & Independent symbolic events & Source outcomes\\\midrule']
for name in NAMES:
    r=json.loads((ROOT/'machines'/name/'independent/receipt.json').read_text())
    lines.append(f"{name} & {r['symbolic_steps']:,} & {r['source_outcomes']:,} "+r'\\')
lines += [r'\bottomrule\end{tabular}\end{center}',
          r'\paragraph{Exact dense-table SHA-256 identifiers.}']
for name in NAMES:
    h=hashlib.sha256((ROOT/'machines'/name/'machine.tm').read_bytes()).hexdigest()
    lines += [r'\noindent\textbf{'+name+r'}\par{\small\path{'+h+r'}}\par']
(HERE/'metrics.tex').write_text('\n'.join(lines)+'\n')

lines=[]
for name in NAMES:
    rows={}
    for line in(ROOT/'machines'/name/'machine.tm').read_text().splitlines():
        q,b,w,d,n=line.split();rows[int(q),int(b)]=w+d+n
    lines += ([r'\clearpage'] if name!=NAMES[0] else [])
    lines += [r'\subsection{'+name+'}',
              r'\begin{center}\fontsize{8.5}{9.3}\selectfont',
              r'\setlength{\tabcolsep}{5pt}\renewcommand{\arraystretch}{1.03}',
              r'\begin{tabular}{rll@{\hspace{12pt}}rll@{\hspace{12pt}}rll@{\hspace{12pt}}rll}',
              r'\toprule',
              r'$q$ & read 0 & read 1 & $q$ & read 0 & read 1 & $q$ & read 0 & read 1 & $q$ & read 0 & read 1\\\midrule']
    for i in range(49):
        cells=[]
        for q in(i,i+49,i+98,i+147):
            cells += [str(q),r'\texttt{'+rows[q,0]+'}',r'\texttt{'+rows[q,1]+'}'] if q<194 else ['','','']
        lines.append(' & '.join(cells)+r'\\')
    lines += [r'\bottomrule\end{tabular}\end{center}']
(HERE/'transition_tables.tex').write_text('\n'.join(lines)+'\n')

families=list(csv.DictReader((ROOT/'comparison/mechanism_families.csv').open()))
lines=[r'{\small\setlength{\tabcolsep}{4pt}\renewcommand{\arraystretch}{1.12}',
       r'\begin{longtable}{@{}>{\raggedright\arraybackslash}p{0.22\textwidth}>{\raggedright\arraybackslash}p{0.32\textwidth}>{\raggedright\arraybackslash}p{0.40\textwidth}@{}}',
       r'\toprule Family & Designs & Behavior and proof obligation\\\midrule\endfirsthead',
       r'\toprule Family & Designs & Behavior and proof obligation\\\midrule\endhead']
for r in families:
    names=esc(r['designs']).replace('; ',r';\allowbreak ')
    body=esc(r['recurring_behavior'])+r'\par\emph{Physical change:} '+esc(r['physical_change'])+r'\par\emph{Obligation:} '+esc(r['proof_obligation'])
    lines.append(esc(r['family'])+' & '+names+' & '+body+r'\\\addlinespace')
lines += [r'\bottomrule\end{longtable}}']
(HERE/'families.tex').write_text('\n'.join(lines)+'\n')
print('Generated metrics, three complete tables, and',len(families),'comparison groups.')
