#!/usr/bin/env python3
"""Generate the report's tables from the delivered literal artifacts."""
import json,math
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent

def esc(s):
    mapping={'\\':r'\textbackslash{}','&':r'\&','%':r'\%','$':r'\$','#':r'\#','_':r'\_',
             '{':r'\{','}':r'\}','~':r'\textasciitilde{}','^':r'\textasciicircum{}',
             '→':r'$\to$','≤':r'$\le$','≥':r'$\ge$','Σ':r'$\Sigma$','₁':'1','–':'--','—':'---'}
    return ''.join(mapping.get(c,c)for c in str(s))

def literal(path,out):
    rows={}
    for line in path.read_text().splitlines():
        if not line.strip()or line.startswith('#'):continue
        q,b,w,d,n=line.split();rows[int(q),int(b)]=w+d+n
    assert len(rows)==388
    lines=[r'\begin{center}\small',r'\setlength{\tabcolsep}{4.5pt}',r'\renewcommand{\arraystretch}{1.04}',
           r'\begin{tabular}{@{}rll@{\quad}rll@{\quad}rll@{\quad}rll@{}}',r'\toprule',
           r'$q$&read 0&read 1&$q$&read 0&read 1&$q$&read 0&read 1&$q$&read 0&read 1\\\midrule']
    for i in range(49):
        cells=[]
        for block in range(4):
            q=i+49*block
            cells.extend([str(q),r'\texttt{'+rows[q,0]+'}',r'\texttt{'+rows[q,1]+'}'] if q<194 else ['','',''])
        lines.append('&'.join(cells)+r'\\')
    lines += [r'\bottomrule\end{tabular}\end{center}']
    out.write_text('\n'.join(lines)+'\n')

def designs():
    items=json.loads((ROOT/'comparison/all_194_designs.json').read_text())
    categories={'reported principal construction':'Principal','supplementary construction':'Supplement',
                'research auxiliary':'Research','research seed':'Seed','rejected':'Rejected','rejected diagnostic':'Diagnostic'}
    lines=[r'\begingroup\fontsize{9}{10}\selectfont\setlength{\tabcolsep}{4pt}\setlength{\parskip}{0pt}',
           r'\begin{longtable}{@{}p{0.27\linewidth}p{0.12\linewidth}p{0.56\linewidth}@{}}',
           r'\toprule Design / class prefix & Category & Mechanism or reason for retention\\\midrule\endfirsthead',
           r'\toprule Design / class prefix & Category & Mechanism or reason for retention\\\midrule\endhead']
    for x in items:
        name=esc(x['name'])+r'\newline{\scriptsize\texttt{'+x['canonical_class'][:12]+'}}'
        lines.append(name+'&'+categories[x['category']]+'&'+esc(x['mechanism'])+r'\\[3pt]')
    lines += [r'\bottomrule\end{longtable}\endgroup']
    (HERE/'design_ledger.tex').write_text('\n'.join(lines)+'\n')

def packets():
    items=json.loads((ROOT/'comparison/packet_ledger87.json').read_text())
    lines=[r'\begingroup\footnotesize\setlength{\tabcolsep}{4pt}',
           r'\begin{longtable}{@{}p{0.43\linewidth}p{0.52\linewidth}@{}}',
           r'\toprule Delivery & Attributed result\\\midrule\endfirsthead',
           r'\toprule Delivery & Attributed result\\\midrule\endhead']
    for i,x in enumerate(items,1):
        name=str(i)+'. '+r'\nolinkurl{'+x['packet']+'}'+r'\newline '+esc(x['location'])
        lines.append(name+'&'+esc(x['reported_result'].replace('`',''))+r'\\[5pt]')
    lines += [r'\bottomrule\end{longtable}\endgroup']
    (HERE/'packet_ledger.tex').write_text('\n'.join(lines)+'\n')

if __name__=='__main__':
    literal(ROOT/'machines/SEL/machine/pa194sel.tm',HERE/'sel_table.tex')
    literal(ROOT/'machines/AX11GH/machine/machine.tm',HERE/'ax11gh_table.tex')
    designs();packets()
