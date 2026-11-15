#!/usr/bin/env python3
"""Generate exact comparison and transition appendices from delivered artifacts."""
from pathlib import Path
import csv
ROOT=Path(__file__).resolve().parents[1]
def tex(s):
 return ''.join({'\\':r'\textbackslash{}','_':r'\_','&':r'\&','%':r'\%','#':r'\#','$':r'\$','{':r'\{','}':r'\}'}.get(c,c) for c in s)
rows=list(csv.DictReader((ROOT/'comparison/frontier194_annotated.csv').open()))
roles={'reported principal construction':'P','principal construction':'P','supplementary construction':'S','research auxiliary':'A','research seed':'B','rejected':'R','diagnostic control':'D'}
out=[r'\begingroup\small',r'\begin{longtable}{@{}r l p{0.55\linewidth} c@{}}',r'\toprule No. & Class prefix & Name or representative role & Role\\\midrule\endfirsthead',r'\toprule No. & Class prefix & Name or representative role & Role\\\midrule\endhead']
for i,r in enumerate(rows,1):
 out.append(f"{i} & \\texttt{{{r['table_class'][:12]}}} & {tex(r['name'])} & {roles[r['role']]} \\")
 out[-1]+='\\'
out.extend([r'\bottomrule\end{longtable}',r'\endgroup'])
(ROOT/'report/inventory_table.tex').write_text('\n'.join(out)+'\n')
out=[]
for j,name in enumerate(('PA194AX11H_SF','PA194LC_AX11H_SF')):
 if j:out.append(r'\clearpage')
 out.append(r'\subsection*{'+tex(name)+'}')
 rows={}
 for line in (ROOT/'composites/machines'/name/'machine.tm').read_text().splitlines():
  q,b,w,d,n=line.split();rows[int(q),int(b)]=w+d+n
 assert len(rows)==388 and set(rows)=={(q,b) for q in range(194) for b in (0,1)}
 out.extend([r'\begin{center}',r'\begingroup\ttfamily\fontsize{9}{10.4}\selectfont',r'\setlength{\tabcolsep}{4pt}',r'\begin{tabular}{rll@{\hspace{1.2em}}rll@{\hspace{1.2em}}rll@{\hspace{1.2em}}rll}',r'\toprule q & 0 & 1 & q & 0 & 1 & q & 0 & 1 & q & 0 & 1\\\midrule'])
 for i in range(49):
  chunks=[]
  for base in (0,49,98,147):
   q=base+i
   chunks.append(f'{q} & {rows[q,0]} & {rows[q,1]}' if q<194 else ' & & ')
  out.append(' & '.join(chunks)+r'\\')
 out.extend([r'\bottomrule\end{tabular}',r'\endgroup\end{center}'])
(ROOT/'report/transition_tables.tex').write_text('\n'.join(out)+'\n')
print('Generated complete 140-class inventory and both 388-transition tables.')
