#!/usr/bin/env python3
"""Regenerate report data directly from frozen receipts and comparison files."""
from pathlib import Path
import json
R=Path(__file__).resolve().parent;P=R.parent
load=lambda p:json.loads((P/p).read_text())
def esc(s):
 return ''.join({'&':r'\&','%':r'\%','$':r'\$','#':r'\#','_':r'\_','{':r'\{','}':r'\}','~':r'\textasciitilde{}','^':r'\textasciicircum{}','\\':r'\textbackslash{}'}.get(c,c)for c in str(s))
def put(n,s):(R/n).write_text(s+'\n')
C=load('comparison/summary.json')['counts'];V=load('machine/independent/receipt.json')
put('census_summary.tex',r'''The present literal census has \textbf{1490 occurrences}, \textbf{731
byte forms}, and \textbf{502 spanning one-halt graph classes}, together with
three separately flagged diagnostic table types. Among them are exactly
\textbf{42 distinct 194-state classes}: 28 reported constructions, nine
auxiliary research tables, and five explicitly rejected tables. The small
4-, 6-, and 9-control diagnostic fixtures are not consistency machines.
The remaining state-count distribution is retained in
\file{comparison/summary.json}; it includes numerous mutants and repeated
research families and must not be read as a list of proved machines.''')
assert(C['occurrences'],C['byte_forms'],C['frontier_194_graph_classes'])==(1490,731,42)
N=load('comparison/pa194qh_novelty.json');assert N['candidate']['structurally_new']and N['frontier_tables']==42
put('novelty_summary.tex',r'''The exact comparison returns \emph{no match} for PA194QH against all
42 prior representatives. As a positive control, the tentative Q+C
construction was recognized as exactly PA194Q, with identical dense bytes;
its rejected novelty receipt is retained. The accepted QH receipt records
its full table hash and 194 reachable controls. This check establishes
structural nonidentity under the stated relation, not semantic inequivalence
of the halting predicates (which are intentionally equivalent).''')
put('verification_summary.tex',r'''The construction checker verifies 4754 outcomes in 1\,541\,456 symbolic
iterations. The independent literal checker verifies the same 4754 outcomes
in \textbf{1\,125\,793 symbolic operations}, with at most 403 operations for
one outcome. Its minimum constant term in the positive physical-duration
certificates is 3, and it rederives all four list-sweep lemmas from the
candidate rows. These operation counts refer to the respective symbolic
algorithms, not to equal notions of elapsed TM time. Both checks return
\texttt{PASS}; the complete per-outcome certificates are delivered.''')
assert(V['symbolic_steps'],V['maximum_symbolic_steps'],V['minimum_positive_duration_constant'])==(1125793,403,3)
put('search_summary.tex',r'''Two bounded searches revisited the existing split-macro approach.
The first exposed each D/H/A copy as a shared Push prefix followed by its
loader; the second also exposed the closed phases of Push and constructor
arithmetic, with exact existing reader pairs available without a new
control. These are credited extensions/replays of an existing strategy,
not a new method. Each run had a 240-second budget.
\begin{center}\small
\begin{tabular}{@{}lrrr@{}}
\toprule
Search & Proposals & Accepted slots & Best fitness \\
\midrule
Copy fragments & 3\,966\,253 & 708\,450 & 194 \\
Closed phases & 4\,215\,199 & 222\,291 & 194 \\
\bottomrule
\end{tabular}
\end{center}
Across 8\,181\,452 proposal slots neither run reached the prospective
193-state gate. An independent resolver checked all 60 retained endpoint
grammars and proved their complete resolved 3673-instruction graphs equal
to the baseline. This verifies source binding only; the 60 endpoints are
not all newly certified literal machines.

Six further logical-emitter searches tried genuine antecedent exchanges
in the two membership-rewrite heads, parameter permutations, and alternative
separation matrices. The matrix words received independent full-emitter
free-term checks. The searches completed 30\,600\,000 proposed mutations;
the best allocator count was 196. The 197--200 results for the rewrite-head
searches are optimistic pair-matching scores; only the two matrix endpoints
at 196 also passed the evaluator's simultaneous-fold compatibility check.
None underwent full physical acceptance, and none is claimed as a new
machine. The frozen source, inputs, witnesses, logs, and these distinctions
are in \file{search/logic/}.

Proposal slots may repeat a tree, be no-ops, or be skipped. Neither total
counts distinct machines. All conclusions are limited to the specified
finite heuristic searches. They establish no global lower bound and do not
rule out a mathematically different route below 194.''')
front=load('comparison/frontier194_annotated.json')
lines=[r'\small',r'\begin{longtable}{@{}p{0.245\linewidth}p{0.14\linewidth}p{0.55\linewidth}@{}}',r'\toprule Machine / class & Category & Distinguishing mechanism \\',r'\midrule\endhead']
for row in front:
 name=esc(row['name']);cl=row['table_class'][:10]
 cat={'reported construction':'Reported','auxiliary':'Auxiliary','rejected':'Rejected'}[row['evidence_category']]
 lines.append(name+r'\newline\texttt{'+cl+'} & '+cat+' & '+esc(row['change'])+r' \\[2pt]')
lines.extend([r'\bottomrule\end{longtable}',r'\normalsize']);put('frontier_table.tex','\n'.join(lines))
pack=load('comparison/packet_ledger.json')
lines=[r'\small',r'\begin{longtable}{@{}rp{0.42\linewidth}p{0.47\linewidth}@{}}',r'\toprule No. & Packet & Reported contribution \\',r'\midrule\endhead']
for i,row in enumerate(pack,1):
 name=row['packet'];desc=row['reported_result']
 # The complete packet stem remains available; xurl provides safe legal breaks.
 lines.append(str(i)+r' & \nolinkurl{'+name+r'}\newline\emph{'+esc(row['origin'])+'} & '+esc(desc)+r' \\[2pt]')
lines.extend([r'\bottomrule\end{longtable}',r'\normalsize']);put('packet_table.tex','\n'.join(lines))
rows={}
for ln in(P/'machine/machine.tm').read_text().splitlines():
 q,b,w,d,t=ln.split();rows[int(q),int(b)]=f'{w}{d}{t}'
lines=[r'\small\ttfamily',r'\begin{longtable}{@{}rll@{\hspace{2.5em}}rll@{}}',r'\toprule $q$ & read 0 & read 1 & $q$ & read 0 & read 1 \\',r'\midrule\endhead']
for q in range(97):
 r=q+97;lines.append(f'{q} & {rows[q,0]} & {rows[q,1]} & {r} & {rows[r,0]} & {rows[r,1]}'+r' \\')
lines.extend([r'\bottomrule\end{longtable}',r'\normalfont\normalsize']);put('transition_table.tex','\n'.join(lines))
print('Generated six report fragments and the complete 388-action table.')
