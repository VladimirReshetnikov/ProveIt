"""Standard-library reconstruction of the row-defect first-gap certificates."""
from fractions import Fraction as Q
from itertools import combinations_with_replacement
from pathlib import Path
import json

ZERO=(0,)*5
def C(x):return {ZERO:Q(x)} if x else {}
def var(i):
    t=[0]*5;t[i]=1;return {tuple(t):Q(1)}
def add(*ps):
    out={}
    for p in ps:
        for e,x in p.items():out[e]=out.get(e,Q(0))+x
    return {e:x for e,x in out.items() if x}
def scale(p,x):return {e:y*x for e,y in p.items() if y*x}
def mul(p,q):
    out={}
    for a,x in p.items():
        for b,y in q.items():
            e=tuple(i+j for i,j in zip(a,b));out[e]=out.get(e,Q(0))+x*y
    return {e:x for e,x in out.items() if x}
def power(p,k):
    x=C(1)
    for _ in range(k):x=mul(x,p)
    return x
def pair_rank(a,b):return any(a>>i&1 and b>>j&1 for i in range(3) for j in range(3) if i!=j)
def support_pair(a,b):return sum(pair_rank(a&m,b&m) for m in [3,5,6])

def run():
    n,p,q,d,e=[var(i) for i in range(5)]
    b=add(p,scale(d,-1));m=add(n,scale(e,-1));pp=mul(p,p);nq=mul(n,q);eb=mul(e,b)
    gens=[add(n,C(-4)),add(p,scale(n,-2),C(3)),add(q,scale(n,-1),C(2)),add(scale(q,3),scale(p,-2)),e,add(m,C(-3)),d,add(b,scale(m,-1)),
          add(d,scale(mul(e,m),-1)),add(q,scale(eb,-1)),add(q,eb,scale(d,-2)),add(scale(pp,2),scale(nq,-3)),
          add(mul(n,add(n,C(-1))),scale(mul(e,add(e,C(-1))),-1),scale(p,-2)),
          add(mul(m,add(m,C(-1))),scale(b,-2)),
          add(scale(mul(pp,add(n,C(-2))),2),scale(mul(mul(n,add(n,C(-1))),q),-3)),
          add(mul(mul(n,add(n,C(-1))),add(n,C(-2))),scale(q,-6)),
          add(scale(mul(mul(p,b),m),4),scale(mul(n,mul(b,b)),-2),scale(mul(q,mul(m,m)),-3)),
          add(scale(pp,2),scale(nq,-3),scale(mul(d,d),-2),scale(mul(e,q),4)),
          add(mul(mul(m,add(m,C(-1))),add(m,C(-2))),scale(eb,6),scale(q,-6))]
    c0=add(q,scale(p,3),scale(n,3),C(1),scale(d,-1),scale(e,-2))
    def kappa(mask):
        deg=mask.bit_count();out=add(scale(q,deg),scale(p,2 if deg==1 else 3),n)
        return add(out,scale(d,-deg),scale(e,-1)) if not mask&1 else out
    records=json.loads((Path(__file__).resolve().parent.parent/'data'/'degree_one_certificate.json').read_text())['certificates']
    expected={(a,b) for a,b in combinations_with_replacement(range(1,8),2) if pair_rank(a,b)}
    if len(records)!=25:raise RuntimeError('incomplete certificate')
    seen=set();count=0
    for item in records:
        a,bm=item['masks'];seen.add((a,bm))
        lam=add(scale(q,support_pair(a,bm)),p,scale(d,-1) if not (a|bm)&1 else {})
        target=mul(add(n,C(-2)),add(scale(mul(kappa(a),kappa(bm)),16),scale(mul(c0,lam),-15)))
        rebuilt=C(item['margin'])
        if item['margin']!=1:raise RuntimeError('margin changed')
        for term in item['terms']:
            w=Q(term['weight']);powers=term['powers']
            if w<0 or len(powers)!=19 or any(v<0 for v in powers):raise RuntimeError('invalid cone term')
            poly=C(w)
            for g,k in zip(gens,powers):poly=mul(poly,power(g,k))
            rebuilt=add(rebuilt,poly);count+=1
        if rebuilt!=target:raise RuntimeError(('identity mismatch',a,bm))
    if seen!=expected:raise RuntimeError('pair coverage mismatch')
    return {'exact_neighborhood_pair_certificates':25,'nonnegative_terms':count,'strict_remainder':1,'all_passed':True}

if __name__=='__main__':
    result=run();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
