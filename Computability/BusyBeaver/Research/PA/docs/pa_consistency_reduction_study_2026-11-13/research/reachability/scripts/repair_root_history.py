#!/usr/bin/env python3
"""Screen a one-row repair for root rotation's changed node20 history."""
from pathlib import Path
import sys,json,itertools,time
HERE=Path(__file__).resolve().parent
P=HERE.parent/'inputs'
sys.path.insert(0,str(P));import compiler as c
c.ROOT=P
g=c.read_grammar(P/'pa194.grammar.json');s,ins,oldcontracts=c.source(g)
nodes=c.raw_nodes();nodes.update(node21=('node20','node170'),node171=('node21','node23'),node172=('node7','node171'),node162=('node37','node163'),node164=('node75','node162'));c.raw_nodes=lambda:nodes
ss,ii,cs=c.source(g);assert ins==ii
labels=json.loads((P/'pa194.labels.json').read_text());rows={}
for line in (P/'pa194.tm').read_text().splitlines():
    q,b,w,d,n=line.split();rows[labels[int(q)],int(b)]=(int(w),d=='R',labels[int(n)])
affected=[]
for i,co in enumerate(oldcontracts):
    hit=[]
    def observe(x):
        if x[0]==69:hit.append(True)
    assert c.run(rows,co,observe=observe)is not None
    if hit:affected.append(i)
rows.update({(84,0):(0,True,68),(53,0):(0,True,69),(53,1):(1,True,214),(310,0):(0,True,53),(100,0):(0,True,213),(100,1):(1,True,174),(174,0):(0,True,28),(174,1):(1,True,164)})
S=sorted({q for q,b in rows});hits=[];hist={};start=time.monotonic()
affected.sort(key=lambda i:0 if cs[i][0]==11 else 1)
for w,d,n in itertools.product((0,1),(False,True),S):
    rows[69,0]=(w,d,n)
    for j in affected:
        if c.run(rows,cs[j])is None:hist[j]=hist.get(j,0)+1;break
    else:
        hits.append(dict(action=[w,d,n],physical=c.validate(rows,cs)))
out=dict(candidates=4*len(S),affected_contracts=len(affected),hits=hits,first_failure_histogram=hist,seconds=time.monotonic()-start)
(HERE.parent/'receipts/root_history_repair.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
