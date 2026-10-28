#!/usr/bin/env python3
"""Exact certificate checks and finite tests for cached_tree.tex.

The CRT test uses a naive prime-field matrix product as an independent
correctness oracle. It does not implement the imported fast field algorithm.
"""
from __future__ import annotations
from fractions import Fraction as F
from decimal import Decimal, localcontext, ROUND_FLOOR, ROUND_CEILING
from itertools import product
from math import isqrt, log, log2, pi, sqrt
import json
import random
import sys


def need(cond, label):
    if not cond:
        raise RuntimeError(label)


def atan_interval(inv, count=100):
    z = F(1, inv)
    partial = sum(((-1)**k * z**(2*k+1)/F(2*k+1) for k in range(count)), F(0))
    nxt = (-1)**count * z**(2*count+1)/F(2*count+1)
    return min(partial,partial+nxt), max(partial,partial+nxt)


def pi_interval():
    a,b = atan_interval(5)
    c,d = atan_interval(239)
    return 16*a-4*d,16*b-4*c


def log2_interval(count=100):
    # ln 2 = 2 atanh(1/3); positive geometric bound on the omitted tail.
    z=F(1,3)
    partial=2*sum((z**(2*k+1)/F(2*k+1) for k in range(count)),F(0))
    err=2*z**(2*count+1)/(F(2*count+1)*(1-z*z))
    return partial,partial+err


def sqrt_interval(x, digits=30):
    x=F(x); scale=10**digits
    k=isqrt(x.numerator*scale*scale//x.denominator)
    return F(k,scale),F(k+1,scale)


def imul(x,y):
    need(x[0]>=0 and y[0]>=0,'positive interval multiplication')
    return x[0]*y[0],x[1]*y[1]


def idiv(x,y):
    need(x[0]>=0 and y[0]>0,'positive interval division')
    return x[0]/y[1],x[1]/y[0]


def iadd(x,y):return x[0]+y[0],x[1]+y[1]

def scale_i(x,q):return x[0]*q,x[1]*q

def fmt_interval(x):
    endpoints=[]
    for v,rounding in zip(x,(ROUND_FLOOR,ROUND_CEILING)):
        with localcontext() as ctx:
            ctx.prec=80;ctx.rounding=rounding
            d=Decimal(v.numerator)/Decimal(v.denominator)
            endpoints.append(str(d.quantize(Decimal('0.00000000001'))))
    return endpoints


def merge_cost(r,a,b):
    k=a+b;v=[2*a*(r-k),2*a*b,2*b*(r-k)]
    return F(sum(v))-F(21,25)*min(v)


def build_cost(r,k):
    if k==1:return F(2*(r-1))
    a=k//2;b=k-a
    return max(build_cost(r,a),build_cost(r,b),merge_cost(r,a,b))


def check_constants():
    P=pi_interval();L=log2_interval();ratio=idiv(P,L)
    time=scale_i(imul(ratio,sqrt_interval(24339)),F(1,20))
    space=scale_i(imul(ratio,sqrt_interval(915)),F(1,4))
    k0=imul(ratio,sqrt_interval(122))
    k1=scale_i(imul(ratio,sqrt_interval(F(26352,125))),F(1,4))
    a8=scale_i(sqrt_interval(14),F(1,8))
    a12=scale_i(sqrt_interval(22),F(1,12))
    b12=scale_i(sqrt_interval(F(1728,25)),F(1,12))
    gamma=idiv((F(1),F(1)),sqrt_interval(6))
    geometric=idiv(a12,(1-gamma[1],1-gamma[0]))
    tail=iadd(imul(a8,k0),imul(b12,k1))
    tailspace=scale_i(k1,F(2,3))
    need(time[1]<F(3536,100),'time coefficient < 35.36')
    need(space[1]<F(3428,100),'space coefficient < 34.28')
    need(geometric[1]<b12[0],'tail recurrence maximum at first tail depth')
    need(tail[1]<time[0],'root triangle dominates full time')
    need(tailspace[1]<space[0],'root boundary dominates space')
    need(F(1,61)+F(125,13176)/(1-F(1,6))==F(1,36),'cumulative budget')
    need(F(9,10)+F(6,61)==F(609,610),'root power gap')
    need(12**100<2**359,'rational upper bound for log2(12)')
    need(F(9,10)+F(359,100*36)==1-F(1,3600),'tail retained power gap')
    need(F(2*359+100,100*36)<1,'tail fresh and rounding gap')
    need(6**3<5**4,'positive bootstrap exponent eta')
    rows=[]
    for r,ks,expected_merge,expected_tri,expected_mem in [
        (8,[3,3,2],F(766,25),F(798,25),30),
        (12,[4,4,4],F(1632,25),F(1728,25),64)]:
        merge=max(build_cost(r,k) for k in ks)
        vs=[2*ks[0]*ks[1],2*ks[0]*ks[2],2*ks[1]*ks[2]]
        triangle=F(sum(vs))-F(21,25)*min(vs)
        memory=max(2*k*(r-k) for k in ks)
        need(merge==expected_merge and triangle==expected_tri and memory==expected_mem,'cardinality ledger')
        rows.append({'r':r,'blocks':ks,'merge':str(merge),'triangle':str(triangle),'boundary':memory})
    return {'time_interval':fmt_interval(time),'space_interval':fmt_interval(space),
            'tail_time_interval':fmt_interval(tail),'tail_space_interval':fmt_interval(tailspace),
            'eta':1-.75*log(6)/log(5),'exact_cardinality_ledger':rows,
            'interval_method':'Machin alternating sums, positive atanh tail, integer square roots; rational comparisons'}


def primes():
    k=3
    while True:
        if all(k%d for d in range(2,isqrt(k)+1)):
            yield k
        k+=2


def matmul(A,B,mod=None):
    out=[[sum(A[i][k]*B[k][j] for k in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]
    return [[x%mod for x in row] for row in out] if mod else out


def crt_product(A,B):
    bound=len(B)*max(max(row) for row in A)*max(max(row) for row in B)
    result=[[0]*len(B[0]) for _ in A]; modulus=1;used=[]
    for q in primes():
        C=matmul(A,B,q)
        for i in range(len(A)):
            for j in range(len(B[0])):
                delta=(C[i][j]-result[i][j])*pow(modulus,-1,q)%q
                result[i][j]+=modulus*delta
        modulus*=q;used.append(q)
        if modulus>bound:break
    return result,used


def ring_mul(x,y,mod,ell):
    # Basis V^j, U V^j, f(U)=U^2+U+1, V^ell=0.
    out=[0]*(2*ell)
    for j in range(ell):
        for k in range(ell-j):
            aa=x[2*j]*y[2*k];ab=x[2*j]*y[2*k+1]+x[2*j+1]*y[2*k]
            bb=x[2*j+1]*y[2*k+1]
            out[2*(j+k)]+=aa-bb;out[2*(j+k)+1]+=ab-bb
    return tuple(c%mod for c in out)


def check_crt():
    rng=random.Random(20261026);checks=0;max_primes=0
    for p in (1,2,5,9):
        mod=1<<p
        for ell in (1,2,3):
            dim=2*ell
            for n,m,k in ((1,1,1),(2,3,2),(3,2,4)):
                A=[[tuple(rng.randrange(mod) for _ in range(dim)) for _ in range(m)] for _ in range(n)]
                B=[[tuple(rng.randrange(mod) for _ in range(dim)) for _ in range(k)] for _ in range(m)]
                direct=[[tuple(sum(ring_mul(A[i][t],B[t][j],mod,ell)[h] for t in range(m))%mod for h in range(dim)) for j in range(k)] for i in range(n)]
                reconstructed=[[[0]*dim for _ in range(k)] for _ in range(n)]
                basis=[tuple(int(i==j) for i in range(dim)) for j in range(dim)]
                for u in range(dim):
                    for v in range(dim):
                        I=[[x[u] for x in row] for row in A];J=[[x[v] for x in row] for row in B]
                        C,ps=crt_product(I,J);max_primes=max(max_primes,len(ps))
                        need(C==matmul(I,J),'integer-coordinate CRT product')
                        structure=ring_mul(basis[u],basis[v],mod,ell)
                        for i in range(n):
                            for j in range(k):
                                for h in range(dim):reconstructed[i][j][h]+=C[i][j]*structure[h]
                result=[[tuple(z%mod for z in x) for x in row] for row in reconstructed]
                need(result==direct,'quotient-ring coordinate reconstruction');checks+=1
    return {'quotient_ring_matrix_tests':checks,'max_CRT_primes':max_primes,'backend':'naive field multiplication used as correctness oracle, not fast backend'}


def check_tables():
    rng=random.Random(90125);checks=0;mod=32
    for r in (4,5,6,8,12):
        all_edges=[(g,h) for g in range(r) for h in range(r) if g!=h]
        for rep in range(4):
            active=set(rng.sample(all_edges,min(8,len(all_edges))))
            edges=tuple(sorted(active))
            axes={g:tuple(e for e in edges if g in e) for g in range(r)}
            caches={g:{v:rng.randrange(mod) for v in product((0,1),repeat=len(axes[g]))} for g in range(r)}
            total=0
            for vals in product((0,1),repeat=len(edges)):
                index=dict(zip(edges,vals));term=1
                for g in range(r):term=term*caches[g][tuple(index[e] for e in axes[g])]%mod
                total=(total+term)%mod
            def build(S):
                if len(S)==1:
                    g=next(iter(S));return axes[g],caches[g]
                sortedS=sorted(S);a=set(sortedS[:len(S)//2]);b=S-a
                ax,X=build(a);ay,Y=build(b)
                shared=tuple(sorted(set(ax)&set(ay)));external=tuple(sorted(set(ax)^set(ay)))
                out={}
                for vals in product((0,1),repeat=len(external)):
                    index=dict(zip(external,vals));value=0
                    for internal in product((0,1),repeat=len(shared)):
                        index.update(zip(shared,internal))
                        value+=X[tuple(index[e] for e in ax)]*Y[tuple(index[e] for e in ay)]
                    out[vals]=value%mod
                return external,out
            final_axes,table=build(set(range(r)))
            need(final_axes==() and table[()]==total,'binary subset table contraction');checks+=1
    return {'binary_table_vs_full_enumeration':checks,'ring_modulus':mod,'nontrivial_directed_axes_per_test':8}


def main():
    result={'status':'PASS','constants':check_constants(),'crt':check_crt(),'tables':check_tables(),
            'scope':'Finite interface validation; asymptotic proof is in cached_tree.tex. No end-to-end SAT implementation or fast-matrix backend is claimed.'}
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
