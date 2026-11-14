#!/usr/bin/env python3
"""Exact 16-world countermodel to moving Delta,V through the outer U.

Uses PA196's numerical constructors, including transposed U and code-zero
aliasing. Checks the retained common core; neither complete gate theory is
claimed valid in this model. Requires only Python's standard library.
"""
from functools import lru_cache
from itertools import product
from math import isqrt
import argparse
import json
from pathlib import Path

def require(ok,message):
    if not ok:raise ValueError(message)

WORLDS=list(product((0,1),repeat=4))  # x0,x1,x2,color
INDEX={w:i for i,w in enumerate(WORLDS)}
FULL=(1<<len(WORLDS))-1

def pair(a,b):return (a+b)*(a+b+1)//2+b
def unpair(n):
    s=(isqrt(8*n+1)-1)//2
    b=n-s*(s+1)//2
    return s-b,b
def I(a,b):return 4*pair(a,b)
def M(a,b):return 4*pair(a,b)+1
def U(label,body):return 4*pair(body,label)+2
def E(a,b):return 4*pair(a,b)+3
def N(a):return I(a,1)
def conjunction(a,b):return N(I(a,N(b)))
def imp(a,b):return ((~a)|b)&FULL

REL=[]
for label in range(3):
    edges=[]
    for w in WORLDS:
        ns=[]
        for value in (0,1):
            v=list(w);v[label]=value;v[3]=1-w[3]
            ns.append(INDEX[tuple(v)])
        edges.append(tuple(ns))
    REL.append(edges)

def box_direct(label,mask):
    return sum(1<<w for w,ns in enumerate(REL[label])
               if all(mask&(1<<n) for n in ns))

BOX=[[box_direct(label,mask) for mask in range(FULL+1)] for label in range(3)]
def box(label,mask):return BOX[label][mask]
def exists(label,mask):return FULL^box(label,FULL^mask)

@lru_cache(None)
def value(code):
    if code==0:return FULL
    tag=code%4;a,b=unpair(code//4)
    if tag==0:return imp(value(a),value(b))
    if tag==2:
        require(b<3,'Quantifier outside this finite label set')
        return box(b,value(a))
    require(a<3 and b<3,'Atom outside this finite label set')
    if tag==1:
        return sum(1<<k for k,w in enumerate(WORLDS)
                   if w[3]==0 and w[a]==0 and w[b]==1)
    return sum(1<<k for k,w in enumerate(WORLDS) if w[a]==w[b])

def check():
    require(value(1)==0 and value(I(0,0))==FULL,'Constant/alias mismatch')
    for d in range(3):
        for w,ns in enumerate(REL[d]):
            require(all(w in REL[d][v] for v in ns),'Asymmetric quantifier relation')
        for h in range(FULL+1):
            require(imp(exists(d,box(d,h)),h)==FULL,'h1 counterinstance')
        for a in range(3):
            for h in range(FULL+1):
                require(box(d,box(a,h))==box(a,box(d,h)),'h2 counterinstance')
    for h,d,a in product(range(3),repeat=3):
        require(value(I(M(h,d),I(E(h,a),M(a,d))))==FULL,'h3 counterinstance')
        require(value(I(E(h,d),I(M(a,h),M(a,d))))==FULL,'h4 counterinstance')
    for d,h in product(range(3),repeat=2):
        require(exists(d,value(E(h,d)))==FULL,'h5 counterinstance')
    # Every relation has exactly two successors. All possible A,H values at
    # those successors are covered by these 4*4 local truth assignments.
    for a,h in product(range(4),repeat=2):
        qa=a==3;qh=h==3;qah=((~a|h)&3)==3
        require((not qa) or (not qah) or qh,'h6 counterinstance')
    for a,b,c,u in product((False,True),repeat=4):
        arrow=lambda x,y:(not x)or y
        require(arrow(arrow(arrow(c,u),a),arrow(arrow(a,c),arrow(b,c))),
                'Restricted propositional schema counterinstance')
    a,b,c=0,2,1
    require(c!=a and c!=b,'Guard failed')
    delta=I(E(a,b),U(c,E(a,b)))
    vacuity=I(M(a,b),U(c,M(a,b)))
    point=I(c,M(c,b))
    sep=U(b,conjunction(I(M(a,b),point),I(M(c,b),c)))
    original=N(I(delta,I(vacuity,U(c,I(sep,N(point))))))
    moved=N(U(c,I(delta,I(vacuity,I(sep,N(point))))))
    rows=[]
    for e in (0,1):
        at=INDEX[(0,0,1,e)]
        old=bool(value(original)&(1<<at));new=bool(value(moved)&(1<<at))
        require(old==bool(e) and new==(not bool(e)),'Gate value mismatch')
        rows.append({'color':e,'original_gate':old,'moved_gate':new})
    return {
        'worlds':len(WORLDS),'domain':[0,1],'labels':[0,1,2],
        'h1_h2_truthsets_checked':FULL+1,
        'retained_heads':'all valid; h1/h2 over every truth set, h3/h4/h5 over every label tuple, h6 by all local valuations',
        'parameters':{'a':a,'b':b,'c':c},'environment':[0,0,1],
        'gate_values':rows,
        'scope':'Disproves both common-core implications; does not decide interderivability of the complete gate theories.'
    }

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--receipt',type=Path);args=ap.parse_args()
    output=json.dumps(check(),indent=2)+'\n'
    if args.receipt:args.receipt.write_text(output)
    print(output,end='')
