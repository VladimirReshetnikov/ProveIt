#!/usr/bin/env python3
"""Independent exact schema check by linear reduction of quadratic identities.

This does not import the local compiler. It checks its entire acyclic gate
list, all nine axiom trees, the guarded branch and the product of branches.
"""
from pathlib import Path
from fractions import Fraction
from collections import defaultdict
import json,hashlib
ROOT=Path(__file__).resolve().parent
def require(c,m):
    if not c:raise ValueError(m)
def pp(ts):return {tuple(m):Fraction(c) for c,m in ts if c}
def add(*ps):
    out=defaultdict(Fraction)
    for p in ps:
        for m,c in p.items():out[m]+=c
    return {m:c for m,c in out.items() if c}
def scale(k,p):return {m:k*c for m,c in p.items() if k*c}
def sub(p,q):return add(p,scale(-1,q))
def mul(p,q):
    out=defaultdict(Fraction)
    for m,c in p.items():
        for n,d in q.items():out[tuple(sorted(m+n))]+=c*d
    return {m:c for m,c in out.items() if c}
def V(i):return {(i,):Fraction(1)}
def C(i):return {():Fraction(i)} if i else {}

class Algebra:
    def __init__(self,rows):
        self.basis={}
        self.affine=[]
        for row in rows:
            q=pp(row['terms'])
            q=self.reduce(q,allow_quadratic=True)
            quad=[m for m in q if len(m)==2]
            if not quad:
                if q:self.affine.append(q)
                continue
            pivot=min(quad);a=q[pivot];self.basis[pivot]=scale(1/a,q)
        require(not self.affine,'Unexpected affine dependency in local gates')
    def reduce(self,q,allow_quadratic=False):
        q=dict(q)
        for pivot,row in sorted(self.basis.items()):
            if pivot in q:q=add(q,scale(-q[pivot],row))
        if not allow_quadratic:require(all(len(m)<2 for m in q),'Reference expression is not reduced to a wire')
        return q
    def product(self,a,b):return self.reduce(mul(a,b))
    def square(self,a):return self.product(a,a)

def main():
    folder=ROOT/'stages/local_sparse'
    cert=json.loads((folder/'certificate.json').read_text());rows=cert['new_rows']
    parent_path=ROOT/'source/parent216.json'
    require(hashlib.sha256(parent_path.read_bytes()).hexdigest()==cert['base_sha256'],'parent binding')
    parent=json.loads(parent_path.read_bytes())
    # All original source coordinates are external inputs to this finite
    # gate construction except its two specifically retained output wires.
    known=set(range(216))-set(range(19,96))-{207};outputs=[]
    for row in rows:
        p=pp(row['terms']);unknown={i for mon in p for i in mon}-known
        require(len(unknown)==1,('acyclic target',row['label'],unknown))
        target=unknown.pop()
        require(p.get((target,))==1 and not any(target in m and m!=(target,) for m in p),'unit defining gate')
        known.add(target);outputs.append(target)
    ring=Algebra(rows)
    def pair(a,b):return add(ring.square(add(a,b)),a)
    def I(a,b):return scale(4,pair(a,b))
    def M(a,b):return add(I(a,b),C(1))
    def A(a,b):return add(I(a,b),C(2))
    def E(a,b):return add(I(a,b),C(3))
    def neg(a):return I(a,C(1))
    def exists(a,b):return neg(A(a,neg(b)))
    a,b,c,d=sub(V(8),C(1)),V(9),V(10),V(11)
    req=lambda b,k,h:A(b,I(h,neg(A(b,I(h,neg(M(b,k)))))))
    def closed(a,b,k,h):
        subset=A(k,I(M(k,a),M(k,b)))
        return A(b,I(M(b,k),neg(A(a,I(h,neg(A(a,I(subset,req(b,k,h)))))))))
    rv=I(M(a,b),A(c,M(a,b)))
    seed=A(c,I(closed(a,b,c,c),neg(req(b,c,c))))
    expected=[exists(a,E(a,b)),I(A(a,I(b,c)),I(A(a,b),A(a,c))),
              I(E(a,b),I(M(c,a),M(c,b))),I(A(a,A(b,c)),A(b,A(a,c))),
              I(E(c,a),I(M(c,b),M(a,b))),I(exists(a,A(a,b)),b),
              I(E(c,a),I(E(c,b),A(M(a,b),E(a,b)))),
              I(I(I(c,d),a),I(I(a,c),I(b,c))),neg(I(rv,seed))]
    for j,(want,ts) in enumerate(zip(expected,cert['code_polynomials_before_compact'])):
        require(want==ring.reduce(pp(ts)),('literal axiom tree',j))
    F,S,Sp=V(2),V(12),V(13)
    fs=ring.product(F,S);fps=ring.product(F,Sp);gap=sub(S,Sp)
    factors=[gap]+[ring.reduce(sub(gap,mul(fps,code))) for code in expected[:-1]]
    gp=ring.product(sub(c,a),sub(c,b))
    guard=ring.reduce(sub(mul(gp,gp),mul(add(d,C(1)),add(d,C(1)))))
    bund=ring.reduce(sub(gap,mul(fps,expected[-1])))
    joint=ring.reduce(add(mul(guard,guard),mul(bund,bund)))
    require(joint==ring.reduce(V(79)),'joint guard output')
    m0=ring.reduce(add(C(1),mul(F,I(a,b))))
    m1=ring.reduce(add(S,mul(a,fs)))
    mp=ring.reduce(sub(add(Sp,mul(b,fps)),mul(m0,m1)))
    gen=ring.reduce(sub(add(S,mul(b,fs)),add(Sp,mul(fps,A(a,b)))))
    factors += [mp,gen]
    product=factors[0]
    for factor in factors[1:]:product=ring.product(product,factor)
    require(ring.square(product)==ring.reduce(V(95)),'axis product output')
    # The retained downstream system consumes exactly these two outputs.
    old_private=set(range(19,96))-{79,95}
    kept=[]
    for j,row in enumerate(parent['residuals']):
        if 4<=j<=80:continue
        used={i for _,mon in row['terms'] for i in mon}
        require(not used.intersection(old_private),('old private gate crosses interface',j))
        kept.append(row)
    # The extra old FS definition is harmless and is deleted by a later
    # certified radical projection; no polynomial equality deletion is hidden.
    old_fs=[r for r in kept if r['label']=='shared F times S']
    require(len(old_fs)==1,'old FS definitional extension retained')
    require(pp(old_fs[0]['terms'])==sub(V(207),mul(F,S)),'old FS definition')
    live=sorted({i for r in kept+rows for _,mon in r['terms'] for i in mon})
    require([[i,j] for j,i in enumerate(live)]==cert['renumbering'],'complete compaction mapping')
    ren=dict(cert['renumbering'])
    rebuilt=[dict(r,terms=[[int(c),[ren[i] for i in mon]] for mon,c in sorted(pp(r['terms']).items())]) for r in kept+rows]
    final=json.loads((folder/'equation.json').read_bytes())
    require(rebuilt==final['residuals'],'entire graft residual partition')
    print(json.dumps({'status':'PASS','acyclic_local_gates':len(rows),'constructor_trees':9,'horn_factors':len(factors),
                      'interface_coordinates':[79,95],'retained_rows':len(kept),'graft_rows':len(rebuilt),
                      'method':'independent quadratic-identity elimination over exact rational coefficients'},sort_keys=True))
if __name__=='__main__':main()
