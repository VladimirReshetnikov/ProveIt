"""Exact standard-library replay of all 25 right-neighborhood pair certificates."""
from fractions import Fraction as Q
from itertools import combinations_with_replacement
from pathlib import Path
import json

ZERO=(0,)*6
def c(x):return {ZERO:Q(x)} if x else {}
def var(i):
    a=[0]*6;a[i]=1;return {tuple(a):Q(1)}
def add(*ps):
    out={}
    for p in ps:
        for e,x in p.items():out[e]=out.get(e,Q(0))+x
    return {e:x for e,x in out.items() if x}
def scale(p,x):return {e:v*x for e,v in p.items() if v*x}
def mul(p,q):
    out={}
    for a,x in p.items():
        for b,y in q.items():
            e=tuple(i+j for i,j in zip(a,b));out[e]=out.get(e,Q(0))+x*y
    return {e:x for e,x in out.items() if x}
def power(p,k):
    out=c(1)
    for _ in range(k):out=mul(out,p)
    return out
def pair_rank(a,b):
    return any((a>>i&1) and (b>>j&1) for i in range(3) for j in range(3) if i!=j)
def pair_support(a,b):
    return sum(pair_rank(a&mask,b&mask) for mask in [3,5,6])

def run():
    n,p,q,d1,d2,d3=[var(i) for i in range(6)];ds=[d1,d2,d3]
    pp=mul(p,p);nq=mul(n,q)
    gens=[add(n,c(-3)),add(p,scale(n,-2),c(3)),add(q,scale(n,-1),c(2)),add(scale(q,3),scale(p,-1)),add(p,*[scale(d,-1) for d in ds]),
          *ds,*[add(q,scale(d,-2)) for d in ds],*[add(p,scale(d,-1),scale(n,-2),c(4)) for d in ds],
          add(scale(pp,2),scale(nq,-3)),add(mul(n,add(n,c(-1))),scale(p,-2)),
          add(scale(mul(pp,add(n,c(-2))),2),scale(mul(mul(n,add(n,c(-1))),q),-3)),
          add(mul(mul(n,add(n,c(-1))),add(n,c(-2))),scale(q,-6))]
    C0=add(q,scale(p,3),scale(n,3),c(1),*[scale(d,-1) for d in ds])
    def C1(mask):
        deg=mask.bit_count()
        return add(scale(q,deg),scale(p,2 if deg==1 else 3),n,*[scale(ds[i],-deg) for i in range(3) if not mask>>i&1])
    records=json.loads((Path(__file__).resolve().parent.parent/'data'/'first_gap_certificate.json').read_text())['certificates']
    expected={(a,b) for a,b in combinations_with_replacement(range(1,8),2) if pair_rank(a,b)}
    if len(records)!=len(expected):raise RuntimeError('incomplete pair array')
    seen=set();terms=0
    for item in records:
        a,b=item['masks'];seen.add((a,b))
        C2=add(scale(q,pair_support(a,b)),p,*[scale(ds[i],-1) for i in range(3) if not (a|b)>>i&1])
        gap=add(scale(mul(C1(a),C1(b)),16),scale(mul(C0,C2),-15))
        target=mul(add(n,c(-2)),gap)
        rebuilt=c(item['strict_margin'])
        if item['strict_margin']!=1:raise RuntimeError('strict margin changed')
        for term in item['terms']:
            w=Q(term['weight']);powers=term['powers']
            if w<0 or len(powers)!=18 or any(k<0 for k in powers):raise RuntimeError('invalid certificate term')
            poly=c(w)
            for g,k in zip(gens,powers):poly=mul(poly,power(g,k))
            rebuilt=add(rebuilt,poly);terms+=1
        if rebuilt!=target:raise RuntimeError(('pair identity failed',a,b))
    if seen!=expected:raise RuntimeError('pair coverage failed')
    return {'independent_right_pair_types':len(expected),'exact_cone_terms':terms,'strict_margin':1,'multiplier':'n-2','all_passed':True}

if __name__=='__main__':
    result=run();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
