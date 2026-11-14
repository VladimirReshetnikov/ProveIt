from layout import *
from collections import defaultdict
import time
t=read_grammar('original_grammar.json');rows,index,shape=build(t)
incoming=defaultdict(set)
for (q,b),tr in rows.items():
    if tr[1] and tr[0]==b and tr[2] in shape:incoming[tr[2]].add(b)
left=[q for q in shape if incoming[q]=={0}];right=[q for q in shape if incoming[q]=={1}]
qs={q for q,_ in rows}
provider=[defaultdict(list),defaultdict(list)]
for q in qs:
    for b in (0,1):provider[b][rows[q,b]].append(q)
base=opportunities_fast(rows,shape);basepairs={(a,b) for a,b,o in base}
byselector=defaultdict(set)
for a in left:
    for b in right:
        if (a,b) in basepairs:continue
        differences=[bit for bit in (0,1) if rows[a,bit]!=rows[b,bit]]
        selectors=set()
        for bit in differences:
            here={(u,v) for u in provider[bit][rows[a,bit]] for v in provider[bit][rows[b,bit]] if not {a,b}&{u,v}}
            selectors |= here
        for uv in selectors or []:byselector[uv].add((a,b))
print('base',len(base),'match',len(max_matching(base)),'selectors',len(byselector),flush=True)
best=0
for uv,pairs in byselector.items():
    newrows=rows|{(3000,0):(0,True,uv[0]),(3000,1):(1,True,uv[1])}
    newops=opportunities_fast(newrows,shape,ignore_incoming={3000})
    m=max_matching(newops);score=len(m)-1
    if score>best:best=score;print('BEST',score,uv,'pairs',pairs,'matching',m,flush=True)
    if score<7:continue
    ops=opportunities_fast(newrows,shape)
    # Try greedy repeated folds with current actual edges and matching target.
    for order in [m,list(reversed(m))]:
        rr=dict(newrows);ss=dict(shape);done=[]
        for a,b in order:
            avail=opportunities_fast(rr,ss)
            found=[o for x,y,o in avail if (x,y)==(a,b)]
            if not found:break
            acts=[o[0] for o in found[0]]
            rr=fold(rr,a,b,acts);ss.pop(a);done.append((a,b,acts))
        if len(done)==len(m):
            sites,ins,cs=source(t)
            ans=validate(rr,cs);print('VALIDATION',uv,len(done),ans,flush=True)
            if ans['ok']:
                Path('selector_candidate.json').write_text(json.dumps({'rows':[[q,b,*tr] for (q,b),tr in sorted(rr.items())],'folds':done,'new_selector':uv,'validation':ans},indent=2));raise SystemExit()
