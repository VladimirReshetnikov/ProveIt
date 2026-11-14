#!/usr/bin/env python3
"""Regenerate the report's exact transition and comparison appendices."""
import json
import unicodedata
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
def plain(s):
    for a,b in {'Γ':'Gamma','Σ':'Sigma','ρ':'rho','→':' -> ','↔':' <-> ','≤':' <= ','≥':' >= ','¬':'not ','≠':' != ','–':'-','—':'-','’':"'",'‘':"'",'“':'"','”':'"','×':' x ','₁':'1','₂':'2','₀':'0'}.items():
        s=s.replace(a,b)
    return unicodedata.normalize('NFKD',s).encode('ascii','replace').decode()
def tex(s):
    s=plain(s).replace('`','')
    mapping={'\\':r'\textbackslash{}','&':r'\&','%':r'\%','$':r'\$','#':r'\#','_':r'\_','{':r'\{','}':r'\}','~':r'\textasciitilde{}','^':r'\textasciicircum{}'}
    return ''.join(mapping.get(c,c) for c in s)
def path(s):
    return r'\nolinkurl{'+plain(s).replace('{','').replace('}','')+'}'
for family,loc in [('ax11','primary'),('qh5','secondary_qh5')]:
    rows={}
    for line in (ROOT/loc/'machine/machine.tm').read_text().splitlines():
        q,b,w,d,n=line.split();rows[int(q),int(b)]=f'{w}{d}{n}'
    assert set(rows)=={(q,b)for q in range(194)for b in(0,1)}
    header=' & '.join([r'$q$ & Read 0 & Read 1']*4)
    out=[r'\begingroup\footnotesize\setlength{\tabcolsep}{5pt}',r'\begin{longtable}{@{}rllrllrllrll@{}}',r'\toprule '+header+r'\\\midrule\endfirsthead',r'\toprule '+header+r'\\\midrule\endhead']
    for base in range(49):
        cells=[]
        for block in range(4):
            q=base+49*block
            cells.extend([str(q),rows[q,0],rows[q,1]] if q<194 else ['','',''])
        out.append(' & '.join(cells)+r'\\')
    out += [r'\bottomrule\end{longtable}\endgroup']
    (HERE/f'transition_{family}.tex').write_text('\n'.join(out)+'\n')
packets=json.loads((ROOT/'comparison/packet_ledger.json').read_text())['packets']
out=[r'\begingroup\footnotesize',r'\begin{longtable}{@{}rp{0.39\textwidth}p{0.51\textwidth}@{}}',r'\toprule No. & Delivery & Stated contribution\\\midrule\endfirsthead',r'\toprule No. & Delivery & Stated contribution\\\midrule\endhead']
for i,p in enumerate(packets,1):
    label=p['packet']
    suffix=' (incoming)' if p['location']!='filed' else ''
    out.append(f'{i} & '+path(label)+tex(suffix)+' & '+tex(p['reported_contribution'])+r'\\[5pt]')
out += [r'\bottomrule\end{longtable}\endgroup']
(HERE/'packet_ledger.tex').write_text('\n'.join(out)+'\n')
frontier=json.loads((ROOT/'comparison/frontier194.json').read_text())['classes']
cat={'reported principal construction':'P','supplementary construction':'S','source-validated research rotation':'V','research auxiliary':'A','rejected':'R'}
frontier.sort(key=lambda p:('PSVAR'.index(cat[p['evidence_category']]),p['name']))
out=[r'\begingroup\footnotesize',r'\begin{longtable}{@{}rp{0.31\textwidth}cp{0.54\textwidth}@{}}',r'\toprule No. & Name / graph & Kind & Mechanism\\\midrule\endfirsthead',r'\toprule No. & Name / graph & Kind & Mechanism\\\midrule\endhead']
for i,p in enumerate(frontier,1):
    name=tex(p['name']).replace(r'\_',r'\_\allowbreak ')
    out.append(f'{i} & '+name+r'\newline\texttt{'+p['graph_hash'][:12]+'} & '+cat[p['evidence_category']]+' & '+tex(p['mechanism'])+r'\\[5pt]')
out += [r'\bottomrule\end{longtable}\endgroup']
(HERE/'frontier194.tex').write_text('\n'.join(out)+'\n')
print('Generated 2 complete tables, 66-delivery ledger and 76-class guide.')
