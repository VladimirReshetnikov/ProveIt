"""Sound finite abstract interpretation of zero/nonzero register values on exact source CFG.
The abstract certificate concerns register-source execution only, not literal TM startup/runtime.
"""
from pathlib import Path
from collections import deque, Counter
import json,time
import scan_semantics as s
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
sites=json.loads((ROOT/'baseline/rotation240/sites_logical.json').read_text())
leaf_by_pc={p:i for i,(p,o,r) in enumerate(sites)}
prefix=set(p[:k] for p in leaf_by_pc for k in range(len(p)))
def decode(pc):
    pc=pc.rstrip('0');p='';i=0
    while p in prefix:
        p+=pc[i] if i<len(pc) else '0';i+=1
    assert i>=len(pc)
    return leaf_by_pc[p]
root=decode('')
def nxt(pc):return decode('' if pc is None else pc)
succ=[]
for p,o,r in sites:
    if o=='CH':succ.append(())
    elif o=='CI':succ.append((nxt(s.advance(p)),))
    elif o=='CD':succ.append((nxt(s.advance(s.strip(p,'0',1))),nxt(s.advance(p))))
    elif o=='CB':succ.append((nxt(s.advance(s.strip(p,'0',r))),))
    elif o=='CC':succ.append((decode(s.strip(p,'1',r)),))
    else:raise ValueError(o)
# 1={zero},2={positive},3=arbitrary;0=unreachable.
def moves(i,inp):
    p,o,r=sites[i]
    if o=='CH':return []
    if o=='CI':
        out=list(inp);out[r]=2;return [(succ[i][0],tuple(out))]
    if o=='CD':
        out=[]
        if inp[r]&1:
            a=list(inp);a[r]=1;out.append((succ[i][0],tuple(a)))
        if inp[r]&2:
            a=list(inp);a[r]=3;out.append((succ[i][1],tuple(a)))
        return out
    return [(succ[i][0],inp)]
def solve():
    states=[None]*len(sites);states[root]=tuple(2 if v else 1 for v in (3,0,0,0,3,0,0,0,0))
    todo=deque([root]);inqueue={root};pops=0
    while todo:
        i=todo.popleft();inqueue.remove(i);pops+=1
        for j,out in moves(i,states[i]):
            joined=out if states[j] is None else tuple(a|b for a,b in zip(states[j],out))
            if joined!=states[j]:
                states[j]=joined
                if j not in inqueue:todo.append(j);inqueue.add(j)
    # Independently check inductive containment at every edge.
    for i,inp in enumerate(states):
        if inp is not None:
            for j,out in moves(i,inp):assert all(v&~w==0 for v,w in zip(out,states[j]))
    return states,pops
start=time.monotonic();states,pops=solve()
matches=json.loads((HERE/'conditional_signatures.json').read_text())['matches']
survivors=[]
for m in matches:
    a=m['from_node'];req=m['zero_registers'];occs=[p for p,n in s.D['pathnode'].items() if n==a]
    entries=[decode(p) for p in occs]
    if all(states[i] is None or all(states[i][r]==1 for r in req) for i in entries):
        survivors.append({**m,'occurrences':occs,'entries':entries,'reached_entries':sum(states[i] is not None for i in entries)})
out={'status':'INDUCTIVE_ABSTRACT_SOURCE_INVARIANT','updates':pops,'reachable_sites':sum(x is not None for x in states),
 'singleton_zero_facts':sum(v==1 for x in states if x for v in x),'states':states,'surviving_heuristic_replacements':survivors,
 'seconds':time.monotonic()-start,'scope':'This does not prove finite-sampled semantic replacement identities, literal TM runtime, or source-site input calibration.'}
(HERE/'abstract_zeros.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='states'},indent=2))
