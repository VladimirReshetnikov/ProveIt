#!/usr/bin/env python3
"""Regenerate printed tables directly from the frozen release data."""
from pathlib import Path
import csv

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent

def esc(value):
    value=str(value)
    for a,b in [('→',' -> '),('↔',' <-> '),('≤',' <= '),('≥',' >= '),('Σ','Sigma'),('₁','1'),('Γ','Gamma'),('ρ','rho'),('¬','not '),('–','-'),('—','--'),('’',"'"),('“','"'),('”','"'),('𝗂𝖯𝖱𝖠','iPRA'),('𝖯𝖠','PA')]:
        value=value.replace(a,b)
    return ''.join({'\\':r'\textbackslash{}','&':r'\&','%':r'\%','$':r'\$','#':r'\#','_':r'\_','{':r'\{','}':r'\}','~':r'\textasciitilde{}','^':r'\textasciicircum{}','/':r'/\allowbreak{}'}.get(c,c) for c in value)

def records(name):
    with (ROOT/'comparison'/name).open(newline='') as f:return list(csv.DictReader(f))

def longtable(spec,heading,rows):
    return '\n'.join([r'\begingroup\small',r'\begin{longtable}{'+spec+'}',r'\toprule '+heading+r'\\\midrule\endfirsthead',r'\toprule '+heading+r' (continued)\\\midrule\endhead',r'\bottomrule\endfoot',*rows,r'\end{longtable}',r'\endgroup',''])

families=records('families.csv')
assert len(families)==29
rows=[]
for f in families:
    detail=esc(f['recurring_behavior'])+r' \par\smallskip '+esc(f['designs'])+r' \par\smallskip\emph{Proof obligation:} '+esc(f['proof_obligation'])
    rows.append(esc(f['family'])+' & '+detail+r'\\\addlinespace[5pt]')
(HERE/'family_table.tex').write_text(longtable(r'>{\raggedright\arraybackslash}p{0.23\linewidth}>{\raggedright\arraybackslash}p{0.70\linewidth}','Family & Mechanism and representative designs',rows))

named=records('named_designs.csv');assert len(named)==83
rows=[esc(f['name'])+' & '+esc(f['feature'])+r'\\\addlinespace[4pt]' for f in named]
(HERE/'named_table.tex').write_text(longtable(r'>{\raggedright\arraybackslash}p{0.28\linewidth}>{\raggedright\arraybackslash}p{0.65\linewidth}','Design & Recurring design distinction',rows))

packets=records('packet_ledger.csv');assert len(packets)==97
rows=[]
for i,p in enumerate(packets,1):
    name=p['directory'];assert '{' not in name and '}' not in name
    desc=esc(p['self_description'])
    rows.append(str(i)+' & '+r'\path{'+name+'}'+r' \par\smallskip '+esc(p['location'])+' & '+desc+r'\\\addlinespace[4pt]')
(HERE/'packet_table.tex').write_text(longtable(r'r>{\raggedright\arraybackslash}p{0.39\linewidth}>{\raggedright\arraybackslash}p{0.50\linewidth}','ID & Delivery & Attributed content',rows))

parts=[]
for index,name in enumerate(('PA194LCGMS','PA194LCGSMS')):
    rows={}
    for line in (ROOT/'machines'/name/'machine.tm').read_text().splitlines():
        q,b,w,d,n=line.split();rows[int(q),int(b)]=w+d+n
    assert len(rows)==388 and set(q for q,b in rows)==set(range(194))
    if index:parts.append(r'\clearpage')
    parts.extend([r'\subsection{'+name+'}',r'\begingroup\footnotesize\ttfamily\setlength{\tabcolsep}{4pt}\renewcommand{\arraystretch}{0.94}',r'\begin{longtable}{rll@{\hspace{1.3em}}rll@{\hspace{1.3em}}rll@{\hspace{1.3em}}rll}',r'\toprule q & 0 & 1 & q & 0 & 1 & q & 0 & 1 & q & 0 & 1\\\midrule\endfirsthead',r'\toprule q & 0 & 1 & q & 0 & 1 & q & 0 & 1 & q & 0 & 1\\\midrule\endhead',r'\bottomrule\endfoot'])
    for base in range(49):
        cells=[]
        for group in range(4):
            q=base+group*49
            cells.extend([str(q),rows[q,0],rows[q,1]] if q<194 else ['','',''])
        parts.append(' & '.join(cells)+r'\\')
    parts.extend([r'\end{longtable}',r'\endgroup',''])
(HERE/'transition_tables.tex').write_text('\n'.join(parts))
print('Generated: two complete transition tables, 29 families, 83 named records, 97 packets.')
