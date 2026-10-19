"""Price exact affine substitutions under the parent's proved affine invariant.

Facts are homogeneous row-space generators ordered [1,R0,...,R8]. The source
semantics is total for the small affine class recognized in affine_swaps.py.
Substitution is checked at every expanded occurrence of a shared DAG node.
No new transition-table correctness claim follows from this source check.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import defaultdict
import json,gzip
import source_core as e
import affine_swaps as a

HERE=Path(__file__).resolve().parent
FACTS=[[tuple(map(F,v)) for v in b] if b is not None else []
       for b in json.loads(gzip.decompress((HERE/'affine_facts.json.gz').read_bytes()))]
entries=defaultdict(list)
idx=0
def walk(n):
    global idx
    entries[n].append(idx)
    x=e.S[n]
    if isinstance(x[0],str):idx+=1
    else:walk(x[0]);walk(x[1])
walk(e.ROOT)
assert idx==len(FACTS)==6455

def equivalent(m,n,locs):
    d=[[x-y for x,y in zip(r,s)]for r,s in zip(m,n)]
    seen=set()
    for i in locs:
        for v0 in FACTS[i]:
            if v0 in seen:continue
            seen.add(v0);v=v0[1:]+v0[:1]
            if any(sum(x*y for x,y in zip(row,v)) for row in d):return False
    return True

base=e.score(e.ROOT)
aff={n:a.affine(n)for n in e.live(e.ROOT) if a.affine(n) is not None}
subs=[];com=[];ident=[]
for n,m in aff.items():
    if equivalent(m,a.IDENTITY,entries[n]):ident.append(n)
    for k,p in aff.items():
        if n==k or not equivalent(m,p,entries[n]):continue
        nr=e.replace(e.ROOT,n,k)
        subs.append(dict(source=n,target=k,occurrences=len(entries[n]),score=e.score(nr),
                         source_leaves=len(e.paths(n)),target_leaves=len(e.paths(k))))
for n in sorted(entries):
    x=e.S[n]
    if isinstance(x[0],str)or x[0]==x[1]:continue
    m,p=aff.get(x[0]),aff.get(x[1])
    if m is None or p is None:continue
    if equivalent(a.compose(m,p),a.compose(p,m),entries[n]):
        nr=e.replace(e.ROOT,n,e.cons(x[1],x[0]))
        com.append(dict(source=n,children=x,global_identity=a.compose(m,p)==a.compose(p,m),
                        occurrences=len(entries[n]),score=e.score(nr)))
out=dict(status='EXACT_SOURCE_SEMANTIC_IDENTITIES_ONLY',baseline=base,
         affine_nodes=len(aff),substitutions=sorted(subs,key=lambda r:r['score']),
         identities=ident,commutations=com)
(HERE/'affine_substitutions_replay.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
