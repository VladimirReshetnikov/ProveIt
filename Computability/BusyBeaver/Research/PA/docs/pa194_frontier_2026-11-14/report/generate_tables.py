#!/usr/bin/env python3
"""Generate exact report tables from frozen construction and search receipts."""
from pathlib import Path
import json,re
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
num=lambda n:f'{n:,}'

def read(p):return json.loads(p.read_text())
a=read(ROOT/'machines/AX11G/verification/results/PA194AX11G/receipt.json')
g=read(ROOT/'machines/GH/independent/results/PA194GH/receipt.json')
lines=[r'\begin{center}',r'\begin{tabular}{lrr}',r'\toprule Verified quantity & PA194AX11G & PA194GH\\\midrule']
for label,key in [('Working states','states'),('Transition rows','rows'),('Primitive source sites','source_sites'),('Branch-sensitive source outcomes','source_outcomes'),('Independent symbolic operations','symbolic_steps'),('Maximum symbolic operations / outcome','maximum_symbolic_steps'),('Minimum positive duration constant','minimum_positive_duration_constant'),('Exact blank-start transitions','startup_steps')]:
    lines.append(f'{label} & {num(a[key])} & {num(g[key])} '+r'\\')
lines += [r'\bottomrule\end{tabular}',r'\end{center}',r'The two dense-table SHA-256 values are respectively',r'\begin{quote}\small',r'\nolinkurl{'+a['dense_sha256']+r'}\\',r'\nolinkurl{'+g['dense_sha256']+r'}.',r'\end{quote}']
(HERE/'metrics.tex').write_text('\n'.join(lines)+'\n')

def rows(p):
    d={}
    for line in p.read_text().splitlines():
        if not line.strip() or line.startswith('#'):continue
        q,b,w,dr,n=line.split();d[int(q),int(b)]=(int(w),dr,int(n))
    assert len(d)==388 and {q for q,b in d}==set(range(194))
    return d
aa=rows(ROOT/'machines/AX11G/machine/machine.tm')
gg=rows(ROOT/'machines/GH/machine/machine.tm')
lines=[r'\begingroup\small',r'\begin{longtable}{rcccc}',r'\toprule & \multicolumn{2}{c}{PA194AX11G} & \multicolumn{2}{c}{PA194GH}\\',r'State & Read 0 & Read 1 & Read 0 & Read 1\\\midrule\endhead']
def action(t):return f'${t[0]}\\;{t[1]}\\;{t[2]}$'
for q in range(194):
    lines.append(f'{q} & '+' & '.join(action(d[q,b]) for d in [aa,gg] for b in [0,1])+r'\\')
lines += [r'\bottomrule\end{longtable}',r'\endgroup']
(HERE/'transition_tables.tex').write_text('\n'.join(lines)+'\n')

if (ROOT/'search/offset/summary.json').exists():
    summaries=read(ROOT/'search/offset/summary.json')
    lines=[r'\begin{center}\small',r'\begin{tabular}{lrrrr}',r'\toprule Machine & $\delta=-2$ pairs & $\delta=0$ pairs & $\delta=2$ pairs & Hits\\\midrule']
    for family,rr in summaries['families'].items():
        lines.append(f"{family} & "+' & '.join(num(rr[str(d)]['pairs']) for d in [-2,0,2])+f" & {sum(r['hits'] for r in rr.values())} "+r'\\')
    lines += [r'\bottomrule\end{tabular}\end{center}',
       f"Across these eight tables, the search considered {num(summaries['totals']['pairs'])} admissible pair/displacement instances and {num(summaries['totals']['trials'])} single-row proposals; {num(summaries['totals']['combos'])} surviving two-row combinations were checked jointly. No candidate passed. These counters are search operations, not distinct verified Turing machines. A separate two-state redundant-control positive control recovers its exact one-state quotient."]
    (HERE/'offset_results.tex').write_text('\n'.join(lines)+'\n')

if (ROOT/'search/tags/summary.json').exists():
    tag=read(ROOT/'search/tags/summary.json')
    lines=[r'\begin{center}\small',r'\begin{tabular}{lcrrrr}',r'\toprule Base & $(k,u,e)$ & Proposals & Accepted & Best total score & Sub-194 hits\\\midrule']
    for row in tag['anneals']:
        lines.append(f"{row['base']} & $({row['k']},{row['u']},{row['e']})$ & {num(row['iterations'])} & {num(row['accepted'])} & {row['fixed']+row['best']} & {row['hits']} "+r'\\')
    lines += [r'\bottomrule\end{tabular}\end{center}',
        r'The eight heuristic searches examined a total of '+num(sum(x['iterations'] for x in tag['anneals']))+r' proposals, using both the primary and explicit-binder G emitters. Their best penalized state scores were 196 for the equality-tag-four families and 198 for the swapped-tag family. These are discovery scores; no new positive machine is asserted for them.',
        r'Two new shared-substring MILPs for the equality-tag-four word both reported objective and bound 68 with zero gap: once with only the two-increment macro free, and once also allowing the four-increment macro. The returned dictionaries have exact integer cost 68 and their expansions are independently checked against the 193-token word. This is solver-reported optimality in the stated dictionary model, with a verified feasible witness; no exact branch-and-bound optimality certificate is supplied. The objective omits physical folds and startup and is not a lower bound on machine states.']
    (HERE/'tag_results.tex').write_text('\n'.join(lines)+'\n')
