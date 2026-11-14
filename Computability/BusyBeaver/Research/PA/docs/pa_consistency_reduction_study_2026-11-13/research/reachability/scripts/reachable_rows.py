#!/usr/bin/env python3
"""Conservative source positivity reachability and physical used-row screen."""
from pathlib import Path
from collections import deque,Counter
import json,sys,time,itertools

HERE=Path(__file__).resolve().parent
P=HERE.parent/'inputs'
OUT=HERE.parent/'receipts'
OUT.mkdir(exist_ok=True)
sys.path.insert(0,str(P))
import compiler as c
import symbolic_runtime as sr
c.ROOT=P
g=c.read_grammar(P/'pa194.grammar.json')
sites,ins,contracts=c.source(g)
labels=json.loads((P/'pa194.labels.json').read_text())
rows={}
for line in (P/'pa194.tm').read_text().splitlines():
    q,b,w,d,n=line.split();rows[labels[int(q)],int(b)]=(int(w),d=='R',labels[int(n)])

def successor(i,m):
    v=ins[i];op=v[0]
    if op=='inc':yield v[2],m|(1<<v[1])
    elif op=='dec':
        _,r,z,p=v;b=1<<r
        if m&b:
            yield p,m;yield p,m&~b
        else:yield z,m
    elif op=='jump':yield v[1],m

seen={(25,1)};todo=deque(seen)
while todo:
    i,m=todo.popleft()
    for p in successor(i,m):
        if p not in seen:seen.add(p);todo.append(p)
at=[set() for _ in ins]
for i,m in seen:at[i].add(m)
eligible=[];unused=[]
for co in contracts:
    i,branch,st,en=co
    if not at[i]:unused.append((i,branch,'dead site'));continue
    if branch is not None:
        r,zero=branch;r=c.PHYSICAL.index(r)
        if not any(bool(m&(1<<r))!=zero for m in at[i]):
            unused.append((i,branch,'unreachable branch'));continue
    eligible.append(co)

used={(q,b) for q in c.BOXSTATES for b in (0,1)}
by_state=Counter()
def observer(s):
    q,onl,l,r=s
    b=sr.headbit(l if onl else r)
    if b is not None and (q,b) in rows:used.add((q,b));by_state[q]+=1
lengths=[]
for n,co in enumerate(eligible):
    k=c.run(rows,co,observe=observer)
    assert k is not None,co[:2]
    lengths.append(k)

# The exact initialization prefix ends at the independently established seed.
state,head,ones=74,0,set()
startup_used=set()
for step in range(58154):
    key=state,int(head in ones);startup_used.add(key);used.add(key)
    w,d,state=rows[key]
    (ones.add if w else ones.discard)(head);head+=1 if d else -1
want={-3,46};want.update(-2+j for j,b in enumerate(sites[25][0]) if b)
pos=47
for v in [0,0,0,0,0,0,2,0,0]+[1]*26:
    pos+=1;want.update(range(pos,pos+v+1));pos+=v+1
assert (state,head,ones)==(84,-2,want)
all_states={q for q,b in rows}
dontcare=sorted(set(rows)-used)
hits=[]
for a,b in itertools.combinations(sorted(all_states),2):
    alias=lambda q:b if q==a else q
    acts=[]
    for bit in (0,1):
        aa=rows[a,bit];bb=rows[b,bit]
        aa=aa[:2]+(alias(aa[2]),);bb=bb[:2]+(alias(bb[2]),)
        au=(a,bit) in used;bu=(b,bit) in used
        if au and bu and aa!=bb:break
        acts.append(aa if au else bb)
    else:hits.append(dict(removed=a,kept=b,actions=acts))
out=dict(source_pairs=len(seen),reached_sites=sum(bool(x)for x in at),all_sites=len(sites),eligible_contracts=len(eligible),all_contracts=len(contracts),excluded_contracts=unused,used_rows=len(used),all_rows=len(rows),unused_rows=dontcare,startup_used_rows=len(startup_used),direct_merge_hits=hits,symbolic_operations=sum(lengths),fixed_unused_rows=[x for x in dontcare if x[0]<1300])
(OUT/'screen.json').write_text(json.dumps(out,indent=2)+'\n')
(OUT/'masks.json').write_text(json.dumps([sorted(x)for x in at])+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='excluded_contracts'},indent=2))
