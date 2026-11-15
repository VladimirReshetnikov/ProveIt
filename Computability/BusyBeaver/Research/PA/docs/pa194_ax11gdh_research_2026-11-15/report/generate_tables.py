#!/usr/bin/env python3
"""Regenerate exact report identities, audit metrics, and complete TM tables."""
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parents[1]
TARGETS=[('AX11GDH',ROOT/'machine'),('AX11GDHS',ROOT/'companions/HS/machine'),
 ('AX11GDHF',ROOT/'companions/F/machine'),('AX11GDHR',ROOT/'companions/R/PA194AX11GDHR')]
OUT=ROOT/'report'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 identities=['\\subsection{Byte identities of the dense transition tables}',
  'The following SHA-256 values identify the delivered plain-text tables. '
  'Graph comparison uses exact tuples rather than relying on these hashes.']
 metrics=[r'\begin{center}',r'\small',r'\begin{tabular}{@{}lrrr@{}}',r'\toprule',
 r'Literal replay & Symbolic events & Maximum per outcome & Minimum clock constant\\',r'\midrule']
 tables=[]
 for name,path in TARGETS:
  digest=sha(path/'machine.tm');rec=json.loads((path/'independent/receipt.json').read_text())
  assert rec['dense_sha256']==digest and rec['status']=='PASS'
  identities.extend([r'\par\noindent\begin{minipage}{\linewidth}',r'\textbf{PA194'+name+r'}\par',r'{\small\nolinkurl{'+digest+r'}}',r'\end{minipage}\par'])
  metrics.append(f"{name} & {rec['symbolic_steps']:,} & {rec['maximum_symbolic_steps']} & {rec['minimum_positive_duration_constant']}"+r'\\')
  rows={}
  for line in (path/'machine.tm').read_text().splitlines():
   q,b,w,d,n=line.split();rows[int(q),int(b)]=(int(w),d,int(n))
  assert set(rows)=={(q,b)for q in range(194)for b in (0,1)}
  tables.extend([r'\clearpage',r'\section{Complete dense table: PA194'+name+'}',
   r'Initial control is 0; halt is $H=194$ and is not counted. '
   r'Each entry is $(\text{write},\text{move},\text{next})$. '
   r'The tape is initially all zero; the initial head is at coordinate zero.',
   r'\begin{center}',r'\fontsize{8.1}{9.0}\selectfont',r'\setlength{\tabcolsep}{3.5pt}',
   r'\renewcommand{\arraystretch}{0.98}',
   r'\begin{tabular}{rll@{\hspace{1.8em}}rll@{\hspace{1.8em}}rll}',r'\toprule',
   r'$q$ & Read 0 & Read 1 & $q$ & Read 0 & Read 1 & $q$ & Read 0 & Read 1\\',r'\midrule'])
  for i in range(65):
   cells=[]
   for q in (i,i+65,i+130):
    if q>=194:cells.extend(['','','']);continue
    cells.append(str(q))
    for b in (0,1):
     w,d,n=rows[q,b];cells.append(f'${w}{d}\\,{"H" if n==194 else n}$')
   tables.append(' & '.join(cells)+r'\\')
  tables.extend([r'\bottomrule',r'\end{tabular}',r'\end{center}',r'{\footnotesize SHA-256: \nolinkurl{'+digest+'}}'])
 metrics.extend([r'\bottomrule',r'\end{tabular}',r'\end{center}'])
 for file,lines in [('identities.tex',identities),('verification_metrics.tex',metrics),('transition_tables.tex',tables)]:
  (OUT/file).write_text('\n'.join(lines)+'\n')
 print('Generated all four exact table appendices and audit metrics.')
if __name__=='__main__':main()
