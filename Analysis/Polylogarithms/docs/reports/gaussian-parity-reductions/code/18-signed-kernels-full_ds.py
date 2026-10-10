"""The precisely specified level-four, depth-two linear double-shuffle model.

This is a formal relation module, NOT a model of proven numerical independence.
Colors r,s denote i**r,i**s. We keep imaginary parts, impose conjugation, and
remove the single divergent imaginary coordinate D_{1,w-1}(1,i). Products
with exactly one Li_1(1) contribute stuffle-minus-shuffle cancellation rows.
"""
from __future__ import annotations
from math import comb
import sympy as sp
from gaussian import single_symbol

def canonical(a:int,b:int,r:int,s:int):
    r%=4;s%=4
    if r%2==s%2==0:return None,0
    pair=(r,s);conj=((-r)%4,(-s)%4)
    return ((a,b,*pair),1) if pair<=conj else ((a,b,*conj),-1)

def system(w:int):
    if w<2:raise ValueError("Weight must be at least 2")
    keys=set()
    for a in range(1,w):
        for r in range(4):
            for s in range(4):
                key,_=canonical(a,w-a,r,s)
                if key and not(key[0]==1 and key[2]==0):keys.add(key)
    keys=sorted(keys);index={key:i for i,key in enumerate(keys)}
    rows=[];rhs=[];labels=[]
    def add(terms,value,label):
        d={}
        for coefficient,a,b,r,s in terms:
            key,sign=canonical(a,b,r,s)
            if key:d[key]=d.get(key,0)+coefficient*sign
        d={key:value for key,value in d.items() if value}
        if any(key not in index for key in d):return
        if not d and value==0:return
        row=[0]*len(keys)
        for key,c in d.items():row[index[key]]=c
        rows.append(row);rhs.append(sp.expand(value));labels.append(label)
    for p in range(1,w):
        q=w-p
        for r in range(4):
            for s in range(4):
                stuffle=[(1,p,q,r,s),(1,q,p,s,r)]
                shuffle=[]
                for j in range(p):shuffle.append((comb(q+j-1,j),q+j,p-j,s,r-s))
                for j in range(q):shuffle.append((comb(p+j-1,j),p+j,q-j,r,s-r))
                try:product=sp.expand(sp.im(single_symbol(p,r)*single_symbol(q,s)))
                except ValueError:
                    add(stuffle+[(-c,a,b,r0,s0) for c,a,b,r0,s0 in shuffle],
                        -sp.im(single_symbol(w,r+s)),["regularized",p,q,r,s])
                    continue
                add(stuffle,product-sp.im(single_symbol(w,r+s)),["stuffle",p,q,r,s])
                add(shuffle,product,["shuffle",p,q,r,s])
    return keys,sp.Matrix(rows),sp.Matrix(rhs),labels

def s4_witness():
    keys,A,rhs,labels=system(5)
    target=sp.zeros(len(keys),1)
    for a,c in [(4,3),(3,3),(2,9)]:
        key,sign=canonical(a,5-a,1,0);target[keys.index(key)]+=c*sign
    key,sign=canonical(4,1,1,2);target[keys.index(key)]+=7*sign
    for v in A.nullspace():
        product=(target.T*v)[0]
        if product:
            v=v/product
            assert A*v==sp.zeros(A.rows,1) and (target.T*v)[0]==1
            return keys,A,rhs,labels,target,v
    raise RuntimeError("No obstruction: the formal relation model has changed")
