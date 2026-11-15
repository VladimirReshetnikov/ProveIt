#!/usr/bin/env python3
"""Generate report tables from the delivered exact construction/certificates."""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parents[1]
HERE=Path(__file__).resolve().parent
FAMILIES=('GD','GDH','GDHS')
ALIASES={'GD':'GD194sum','GDH':'GD194H','GDHS':'GD194HS'}
NAMES={x:'PA194'+x for x in FAMILIES}
read=lambda p:json.loads(p.read_text())
meta={x:read(ROOT/'machines'/x/'receipt.json')for x in FAMILIES}
literal={x:read(ROOT/'verification/independent/inputs'/ALIASES[x]/'independent/receipt.json')for x in FAMILIES}

def table(rows):
 t=['\\begin{center}','\\begin{tabular}{lrrr}','\\toprule',' & \\textsf{PA194GD} & \\textsf{PA194GDH} & \\textsf{PA194GDHS}\\\\','\\midrule']
 for title,vals in rows:t.append(title+' & '+' & '.join(format(n,',')if isinstance(n,int)else n for n in vals)+r'\\')
 return '\n'.join(t+['\\bottomrule','\\end{tabular}','\\end{center}'])+'\n'
rows=[('Working controls',[meta[x]['states']for x in FAMILIES]),('Transition rows',[388]*3),('Fixed controls',[134,134,135]),('AX readers',[69]*3),('Simultaneous identifications',[9,9,10]),('Primitive source sites',[meta[x]['source_sites']for x in FAMILIES]),('Source outcomes',[meta[x]['outcomes']for x in FAMILIES]),('Complete blank startup',[meta[x]['startup']['steps']for x in FAMILIES])]
t=table(rows)+'\nThe startup counts are exact initialization times, not uniform speed comparisons.\n'
t+='\n\\noindent The exact dense-table SHA-256 identities are:\n\\begin{quote}\\small\n'
for x in FAMILIES:t+='\\textsf{'+NAMES[x]+'}\\\\\n\\texttt{'+meta[x]['sha256']+'}\\par\\smallskip\n'
t+='\\end{quote}\n'
(HERE/'result_metrics.tex').write_text(t)
rows=[('Source outcomes',[literal[x]['source_outcomes']for x in FAMILIES]),('Independent symbolic steps',[literal[x]['symbolic_steps']for x in FAMILIES]),('Maximum steps per outcome',[literal[x]['maximum_symbolic_steps']for x in FAMILIES]),('Minimum duration constant',[literal[x]['minimum_positive_duration_constant']for x in FAMILIES]),('List lemmas from literal rows',[4]*3),('Literal rows used by contracts',[388]*3)]
t=table(rows)+r'''
Every source branch occurs exactly once in the certificate. All 13 coefficients
of each affine duration vector are nonnegative, and its constant is at least
three. Each nonhalting outcome has zero affine frame displacement, and the
unique halt outcome has exact duration three. All 388 literal transition rows
occur in these symbolic contracts. This is coverage of the arbitrary-frame
contract domain, not a statement that all rows occur in the blank run.
'''
(HERE/'verification_metrics.tex').write_text(t)
fs=read(ROOT/'machines/GD/folds.json')
cs=read(ROOT/'machines/GD/local_cases.json')['cases']
act=lambda v:'$('+str(v[0])+','+('R'if v[1]else'L')+','+str(v[2])+')$'
t=['\\begin{center}\\small','\\begin{tabular}{rrrrr}','\\toprule','Removed & Retained & Read 0 action & Read 1 action & Max. duration\\\\','\\midrule']
for a,b,acts in fs:
 dur=max(v['duration']for v in cs if v['old_state']in(a,b))
 t.append(f'{a} & {b} & {act(acts[0])} & {act(acts[1])} & {dur}'+r'\\')
t+=['\\bottomrule','\\end{tabular}','\\end{center}']
(HERE/'fold_table.tex').write_text('\n'.join(t)+'\n')
parts=[]
for x in FAMILIES:
 rows={}
 for l in(ROOT/'machines'/x/'machine.tm').read_text().splitlines():
  q,b,w,d,n=l.split();rows[int(q),int(b)]=(int(w),d,int(n))
 assert set(rows)=={(q,b)for q in range(194)for b in(0,1)}
 parts+=['\\subsection{'+NAMES[x]+'}',r'\noindent\small\texttt{'+meta[x]['sha256']+'}',r'\normalsize',r'\fontsize{9.5}{11}\selectfont',r'\begin{longtable}{r@{\quad}ll@{\qquad}r@{\quad}ll}',r'\toprule',r'State & On 0 & On 1 & State & On 0 & On 1\\',r'\midrule\endfirsthead',r'\toprule',r'State & On 0 & On 1 & State & On 0 & On 1\\',r'\midrule\endhead',r'\midrule\multicolumn{6}{r}{Continued on next page}\\\endfoot',r'\bottomrule\endlastfoot']
 def fmt(v):return '$('+str(v[0])+','+v[1]+','+str(v[2])+')$'
 for i in range(97):
  j=i+97;parts.append(f'{i} & {fmt(rows[i,0])} & {fmt(rows[i,1])} & {j} & {fmt(rows[j,0])} & {fmt(rows[j,1])}'+r'\\')
 parts +=[r'\end{longtable}',r'\normalsize',r'\clearpage']
(HERE/'transition_tables.tex').write_text('\n'.join(parts)+'\n')
print('Reporttables generatedfromfrozenreceipts')
