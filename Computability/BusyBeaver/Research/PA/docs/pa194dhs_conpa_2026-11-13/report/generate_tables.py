#!/usr/bin/env python3
"""Regenerate exact table, ledger and verification report fragments."""
from pathlib import Path
import json
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
def escape(s):
    replacements={'\\':r'\textbackslash{}','&':r'\&','%':r'\%','$':r'\$','#':r'\#','_':r'\_','{':r'\{','}':r'\}','~':r'\textasciitilde{}','^':r'\textasciicircum{}'}
    return ''.join(replacements.get(c,c) for c in str(s))
def prose(s):
    return ''.join((r'\file{'+p+'}') if i%2 else escape(p) for i,p in enumerate(s.split('`')))
ledger=json.loads((ROOT/'comparison/packet_ledger.json').read_text())
lines=[r'\begingroup\small\setlength{\tabcolsep}{4pt}',r'\begin{longtable}{@{}r p{.36\linewidth} p{.55\linewidth}@{}}',r'\toprule No. & Delivery & Reported contribution\\\midrule\endhead']
for i,x in enumerate(ledger,1):
    name=r'\file{'+x['packet']+'}'
    text=prose(x['reported_contribution'])
    if x['kind']!='filed research packet':text=r'\textbf{Current incoming ZIP.} '+text
    lines.append(f'{i} & {name} & {text}'+r'\\[4pt]')
lines += [r'\bottomrule\end{longtable}\endgroup']
(HERE/'packet_ledger.tex').write_text('\n'.join(lines)+'\n')
frontier=json.loads((ROOT/'comparison/frontier194_annotated.json').read_text())
lines=[r'\begingroup\small\setlength{\tabcolsep}{4pt}',r'\begin{longtable}{@{}p{.20\linewidth} p{.15\linewidth} p{.13\linewidth} p{.43\linewidth}@{}}',r'\toprule Name & Graph prefix & Category & Distinction / status\\\midrule\endhead']
for x in frontier:
    lines.append(' & '.join([escape(x['name']),r'\texttt{'+x['root_free_class'][:12]+'}',escape(x['evidence_category']),prose(x['change'])])+r'\\[4pt]')
lines += [r'\bottomrule\end{longtable}\endgroup',r"Graph prefixes abbreviate the full class hashes in \file{comparison/frontier194_annotated.json}, which also records source locators and exact byte digests. ``Reported construction'' describes the supplied evidence, not fresh validation of every machine."]
(HERE/'frontier194.tex').write_text('\n'.join(lines)+'\n')
rows={}
for line in (ROOT/'machine/machine.tm').read_text().splitlines():
    q,b,w,d,n=line.split();rows[int(q),int(b)]=f'{w}{d}{n}'
assert len(rows)==388
lines=[r'\begingroup\small\setlength{\tabcolsep}{9pt}',r'\begin{longtable}{@{}rll@{\hspace{24pt}}rll@{}}',r'\toprule State & Read 0 & Read 1 & State & Read 0 & Read 1\\\midrule\endhead']
for a in range(97):
    b=a+97
    lines.append(' & '.join([str(a),r'\texttt{'+rows[a,0]+'}',r'\texttt{'+rows[a,1]+'}',str(b),r'\texttt{'+rows[b,0]+'}',r'\texttt{'+rows[b,1]+'}'])+r'\\')
lines += [r'\bottomrule\end{longtable}\endgroup']
(HERE/'transition_table.tex').write_text('\n'.join(lines)+'\n')
r=json.loads((ROOT/'evidence/independent_receipt.json').read_text())
b=json.loads((ROOT/'evidence/build.json').read_text())
facts=[('Working states',194),('Defined binary transitions',388),('Primitive source sites',r['source_sites']),('All-natural source outcomes',r['source_outcomes']),('Literal list lemmas rederived',r['list_lemmas']),('Independent symbolic operations',r['symbolic_steps']),('Largest symbolic operation count for one outcome',r['maximum_symbolic_steps']),('Smallest constant in a physical duration',r['minimum_duration_constant']),('Positivity relation pairs',b['zero_invariant_pairs']),('Exact blank-start transitions',r['startup_steps'])]
lines=[r'\begin{center}\begin{tabular}{@{}lr@{}}\toprule Verification quantity & Result\\\midrule']
for k,v in facts:lines.append(escape(k)+' & '+f'{v:,}'+r'\\')
lines.append(r'\bottomrule\end{tabular}\end{center}')
(HERE/'verification_summary.tex').write_text('\n'.join(lines)+'\n')
print('Regenerated four report fragments from delivered machine and receipts.')
