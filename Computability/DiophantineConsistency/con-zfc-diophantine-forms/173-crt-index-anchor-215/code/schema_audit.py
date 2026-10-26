#!/usr/bin/env python3
"""Standalone bound and local syntax audit for the separated seed calculus.

All arithmetic is exact. This audits finite expression trees and coefficient-
majorant recurrences, not the unbounded consistency theorem.
"""
from __future__ import annotations
from dataclasses import dataclass
from functools import lru_cache
import json

@dataclass(frozen=True)
class Term:
    op: str
    args: tuple

def C(n): return Term('const',(int(n),))
def V(n): return Term('var',(n,))
def add(*xs):
    flat=[]; constant=0
    for x in xs:
        ys=x.args if x.op=='add' else (x,)
        for y in ys:
            if y.op=='const': constant+=y.args[0]
            else: flat.append(y)
    if constant: flat.append(C(constant))
    if not flat: return C(0)
    if len(flat)==1: return flat[0]
    return Term('add',tuple(sorted(flat,key=repr)))
def mul(*xs):
    flat=[]; constant=1
    for x in xs:
        ys=x.args if x.op=='mul' else (x,)
        for y in ys:
            if y.op=='const': constant*=y.args[0]
            else: flat.append(y)
    if not constant: return C(0)
    if constant!=1: flat.append(C(constant))
    if not flat: return C(1)
    if len(flat)==1: return flat[0]
    return Term('mul',tuple(sorted(flat,key=repr)))
def sq(x):
    if x.op=='const': return C(x.args[0]**2)
    return Term('square',(x,))
def sd(x,y): return Term('sqdiff',(x,y))
zero,one,two=C(0),C(1),C(2)
def I(x,y): return mul(two,add(sq(add(x,y)),x))
def M(x,y): return add(I(x,y),one)
def A(x,y): return mul(two,add(sq(add(x,y)),mul(C(3),x),mul(C(4),y),C(3)))
def E(x,y): return add(A(x,y),one)
def N(x): return I(x,one)
def X(x,y): return N(A(x,N(y)))
def req(b,k,h): return A(b,I(h,N(A(b,I(h,N(M(b,k)))))))
def clos(a,b,k,h):
    sub=A(k,I(M(k,a),M(k,b)))
    tail=N(A(a,I(sub,req(b,k,h))))
    tail=N(A(a,I(h,tail)))
    return A(b,I(M(b,k),tail))
def nks(a,b,k): return A(k,I(clos(a,b,k,k),N(req(b,k,k))))
def rv(a,b,c): return I(M(a,b),A(c,M(a,b)))
def bundle(a,b,c): return N(I(rv(a,b,c),nks(a,b,c)))
def seed(c):
    k=add(c,two)
    return N(nks(zero,one,k))
def ordinary(a,b,c,d):
    return [X(a,E(a,b)),I(A(a,I(b,c)),I(A(a,b),A(a,c))),
            I(E(a,b),I(M(c,a),M(c,b))),I(A(a,A(b,c)),A(b,A(a,c))),
            I(E(c,a),I(M(c,b),M(a,b))),I(X(a,A(a,b)),b),
            I(E(c,a),I(E(c,b),A(M(a,b),E(a,b)))),
            I(I(I(c,d),a),I(I(a,c),I(b,c)))]

@lru_cache(None)
def degree(t):
    if t.op=='const': return 0
    if t.op=='var': return 1
    if t.op=='add': return max(map(degree,t.args),default=0)
    if t.op=='mul': return sum(map(degree,t.args))
    if t.op=='square': return 2*degree(t.args[0])
    if t.op=='sqdiff': return 2*max(map(degree,t.args))
    raise ValueError(t.op)

@lru_cache(None)
def bound(t):
    """An exponent e with t <= R**e when every atom <= R and R>=2.

    For sqdiff, t denotes the nonnegative squared difference. Exact cancellation
    is neither required nor used in the bound. All other leaves are nonnegative.
    """
    if t.op=='const':
        n=t.args[0]
        if n<0: raise ValueError('negative leaf')
        return (max(1,n)-1).bit_length()
    if t.op=='var': return 1
    if t.op=='add':
        return max(map(bound,t.args),default=0)+(len(t.args)-1).bit_length()
    if t.op=='mul': return sum(map(bound,t.args))
    if t.op=='square': return 2*bound(t.args[0])
    if t.op=='sqdiff': return 2*(max(map(bound,t.args))+1)
    raise ValueError(t.op)

def dag(t):
    found=set()
    def walk(x):
        if x in found: return
        found.add(x)
        for y in x.args:
            if isinstance(y,Term): walk(y)
    walk(t);return found

def local(old):
    a,b,c,d,S,Sp,F,x,y,u,vq,i=[V(s) for s in ('a','b','c','d','S','Sp','F','x','y','u','vq','i')]
    cs=ordinary(a,b,c,d)
    guard=sd(mul(sd(c,a),sd(c,b)),sq(add(d,one)))
    def weight(z): return add(one,mul(z,F))
    rs=[sd(Sp,S)]+[sd(mul(Sp,weight(z)),S) for z in cs]
    if old:
        cs.append(bundle(a,b,c))
        rs.append(add(sd(mul(Sp,weight(cs[-1])),S),guard))
    else:
        cs.extend([rv(a,b,c),seed(c)])
        rs.extend([add(sd(mul(Sp,weight(cs[-2])),S),guard),sd(mul(Sp,weight(cs[-1])),S)])
    imp,all_=I(a,b),A(a,b)
    rs.extend([sd(mul(Sp,weight(b)),mul(S,weight(a),weight(imp))),
               sd(mul(Sp,weight(all_)),mul(S,weight(b)))])
    horn=mul(*rs)
    den=add(mul(add(i,one),y),one)
    value=add(horn,sd(x,add(S,mul(den,u))),sd(x,add(Sp,mul(add(den,y),vq))))
    labels=add(*cs,a,b,imp,all_,one)
    return value,labels,cs,rs

def metrics(old):
    value,labels,cs,rs=local(old)
    dd=dag(add(value,labels))
    ld=dag(labels)
    return {'local_majorant_exponent':bound(value),'derived_label_majorant_exponent':bound(labels),
            'label_degree':degree(labels),'local_degree_bound':degree(value),
            'source_branches':len(rs),'source_arithmetic_dag_nodes':sum(t.op not in ('const','var') for t in dd),
            'label_arithmetic_dag_nodes':sum(t.op not in ('const','var') for t in ld),
            'code_degrees':[degree(z) for z in cs],
            'code_majorant_exponents':[bound(z) for z in cs],
            'syntax_only_metrics':True}

def main():
    result={'schema':'separated-seed-local-majorants-v1','old':metrics(True),'new':metrics(False),
        'proof_rule':'For R>=2, each nonnegative atom <=R; addition of k terms adds ceil(log2(k)) to the largest exponent, multiplication adds exponents, square doubles them, and (u-v)^2 <= (U+V)^2.',
        'old_inherited_exponents':{'local':2**23,'derived_label':2**22}}
    if not result['new']['local_majorant_exponent']<=2**23: raise RuntimeError('local majorant needs larger budget')
    if not result['new']['derived_label_majorant_exponent']<=2**22: raise RuntimeError('label majorant needs larger budget')
    print(json.dumps(result,indent=2))

if __name__=='__main__': main()
