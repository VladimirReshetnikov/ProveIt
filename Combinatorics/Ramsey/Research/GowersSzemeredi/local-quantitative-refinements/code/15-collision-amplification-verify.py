#!/usr/bin/env python3
"""Reproducible finite checks for collision-sensitive arrangement amplification.

Python 3.10+, standard library only. Combinatorial counts and inequalities use
integers or fractions.Fraction. Only the independently labelled Fourier checks
use floating point. These finite tests supplement, and do not replace, proofs.
Run: python3 verify.py
"""
from __future__ import annotations
from collections import Counter
from fractions import Fraction as F
from itertools import product
from math import prod, pi
from cmath import exp
import json
import random
import time
from pathlib import Path

Point = tuple[int, ...]

class Group:
    def __init__(self, moduli: tuple[int, ...]):
        if not moduli or any(m < 1 for m in moduli):
            raise ValueError('A nonempty tuple of positive moduli is required')
        self.mods = moduli
        self.points = tuple(product(*(range(m) for m in moduli)))
        self.index = {x:i for i,x in enumerate(self.points)}
        self.zero = (0,)*len(moduli)
        self.corners = tuple(product((0,1), repeat=len(moduli)))
        self.signs = tuple((-1)**(len(moduli)-sum(e)) for e in self.corners)
    def add(self, x:Point, y:Point) -> Point:
        return tuple((a+b)%m for a,b,m in zip(x,y,self.mods))
    def sub(self, x:Point, y:Point) -> Point:
        return tuple((a-b)%m for a,b,m in zip(x,y,self.mods))
    def vertices(self, y:Point, h:Point) -> tuple[Point,...]:
        return tuple(tuple((a+e*b)%m for a,b,e,m in zip(y,h,w,self.mods))
                     for w in self.corners)
    def masks(self) -> list[list[int]]:
        return [[sum(1<<i for i in {self.index[v] for v in self.vertices(y,h)})
                 for y in self.points] for h in self.points]


def cartesian_coset(g:Group, A:set[Point]) -> bool:
    if not A: return False
    projections = [set(x[i] for x in A) for i in range(len(g.mods))]
    if prod(map(len,projections)) != len(A): return False
    for P,m in zip(projections,g.mods):
        c = next(iter(P)); H = {(x-c)%m for x in P}
        if any((u-v)%m not in H for u in H for v in H): return False
    return True


def q_count(g:Group, A:set[Point]) -> int:
    return sum(sum(all(v in A for v in g.vertices(y,h)) for y in A)**2
               for h in g.points)


def stability_certificate(g:Group, A:set[Point], Q:int) -> dict:
    a=len(A)
    if not a: raise ValueError('A must be nonempty')
    eps=F(a**3-Q,a**3)
    if not (0 <= eps <= F(1,100)):
        raise ValueError('Not within the theorem threshold')
    r={h:sum(g.add(x,h) in A for x in A) for h in g.points}
    D={h for h in g.points if 8*r[h]>7*a}
    H={g.sub(u,v) for u in D for v in D}
    assert all(g.sub(u,v) in H for u in H for v in H)
    C=max(({g.add(c,h) for h in H} for c in A), key=lambda S:len(S&A))
    b=len(C&A); m=len(C)
    assert b >= (1-8*eps)*a
    assert m <= (1+2*eps)*a
    assert len(A^C) <= 18*eps*a
    assert cartesian_coset(g,C)
    return {'moduli':g.mods, 'size':a, 'Q':Q, 'epsilon':str(eps),
            'coset_size':m, 'symmetric_difference':len(A^C)}


def convolution(a:dict, b:dict, n:int, q:int) -> dict:
    out=Counter()
    for (x,u),v in a.items():
        for (y,w),z in b.items():
            out[((x+y)%n,(u+w)%q)] += v*z
    return dict(out)


def counts_from_m(m_by_h:list[dict], n:int, q:int, max_d:int=8):
    local=[]
    for m in m_by_h:
        vals=[]; conv={(0,0):1}
        for d in range(1,max_d+1):
            conv=convolution(conv,m,n,q)
            vals.append(sum(t*t for t in conv.values()))
        local.append(vals)
    totals=[sum(row[d-1] for row in local) for d in range(1,max_d+1)]
    return totals, local


def make_m(g:Group,n:int,q:int,weights:dict,phi:dict) -> list[dict]:
    ans=[]
    for h in g.points:
        m=Counter()
        for y in g.points:
            vs=g.vertices(y,h)
            for x in range(n):
                w=prod(weights.get((v,x),0) for v in vs)
                if w:
                    val=sum(s*phi[(v,x)] for s,v in zip(g.signs,vs))%q
                    m[(x,val)]+=w
        ans.append(dict(m))
    return ans


def verify_arrangement_case(g:Group,n:int,q:int,weights:dict,phi:dict,
                            fourier:bool=False,constant_label:bool=False):
    m=make_m(g,n,q,weights,phi)
    R,local=counts_from_m(m,n,q)
    C=R[0]
    gamma_cap=sum(sum(weights.get((y,x),0) for y in g.points)**3
                  for x in range(n))
    assert C <= gamma_cap
    for d in range(2,9):
        assert R[1]**(d-1) <= C**(d-2)*R[d-1]
        profile=sum((F(row[1])**(d-1)/F(row[0])**(d-2)
                     for row in local if row[0]),F(0))
        assert profile <= R[d-1]
        if C: assert profile >= F(R[1])**(d-1)/F(C)**(d-2)
    # Every V-valued map has the weak product property gamma=|V|^(-1/8).
    M=len(g.points); k=len(g.mods)
    assert R[1]*n*M**7*q**(2**k) >= C**4
    for d in range(2,9):
        assert (R[d-1]*n**(d-1)*M**(7*d-7)*q**((d-1)*2**k)
                >= C**(3*d-2))
    # The configuration argument also covers vertex-product weights in [0,1].
    b=sum(weights.values()); power=4**k
    assert C*q**(k*4**(k-1))*(M*n)**power >= b**power*M**3*n
    if constant_label:
        # phi=constant has product property gamma=1 for indicator domains.
        M=len(g.points)
        assert R[1]*n*M**7 >= C**4
        for row in local:
            assert row[1]*n*M**4 >= row[0]**4
        for d in range(2,9):
            assert R[d-1]*n**(d-1)*M**(7*d-7) >= C**(3*d-2)
    if fourier:
        spectrum=[]
        for mh in m:
            for r in range(n):
                for u in range(q):
                    z=sum(float(w)*exp(2j*pi*(r*x/n+u*v/q))
                          for (x,v),w in mh.items())
                    spectrum.append(abs(z)**2)
        for d in (1,2,3,8):
            actual=sum(t**d for t in spectrum)
            expected=float(n*q*R[d-1])
            assert abs(actual-expected) <= 1e-9*max(1,expected)
    return R


def verify_labels(g:Group,q:int,phi:dict) -> None:
    def delta(y,h):
        return sum(s*phi[v] for s,v in zip(g.signs,g.vertices(y,h)))%q
    invariant=all(len({delta(y,h) for y in g.points})==1 for h in g.points)
    L={h:delta(g.zero,h) for h in g.points}
    additive=True
    for i,m in enumerate(g.mods):
        for x in g.points:
            for u in range(m):
                for v in range(m):
                    a=list(x);a[i]=u
                    b=list(x);b[i]=v
                    c=list(x);c[i]=(u+v)%m
                    if (L[tuple(a)]+L[tuple(b)]-L[tuple(c)])%q:
                        additive=False
    assert invariant==additive
    for x in g.points:
        remainder=0
        for e in g.corners:
            if all(e): continue
            x_e=tuple(a if t else 0 for a,t in zip(x,e))
            remainder+=(-1)**(len(g.mods)-sum(e)+1)*phi[x_e]
        assert (phi[x]-L[x]-remainder)%q==0



def joint_normal_form(g:Group,n:int,q:int,weights:dict,phi:dict) -> bool:
    fibres={x:{y for y in g.points if weights.get((y,x),0)} for x in range(n)}
    S={x for x,A in fibres.items() if A}
    if not S: return False
    x0=min(S);J={(x-x0)%n for x in S}
    if any((u-v)%n not in J for u in J for v in J): return False
    H0=None;L={}
    for x in S:
        A=fibres[x]
        if not cartesian_coset(g,A): return False
        c=min(A);H={g.sub(y,c) for y in A}
        if H0 is None: H0=H
        if H!=H0: return False
        for h in H:
            vals={sum(s*phi[(v,x)] for s,v in zip(g.signs,g.vertices(y,h)))%q
                  for y in A}
            if len(vals)!=1:return False
            L[(h,x)]=next(iter(vals))
    for h in H0:
        for u in J:
            for v in J:
                if (L[(h,(x0+u+v)%n)]+L[(h,x0)]
                    -L[(h,(x0+u)%n)]-L[(h,(x0+v)%n)])%q:
                    return False
    return True

def main():
    rng=random.Random(20261006)
    stats=Counter(); reports=[]
    started=time.perf_counter()
    for mods in ((2,2),(3,3),(2,2,2),(4,2)):
        g=Group(mods); masks=g.masks(); M=len(g.points)
        eq=0; stable=0
        for A_mask in range(1,1<<M):
            A={g.points[i] for i in range(M) if A_mask>>i&1}
            a=len(A)
            Q=sum(sum((mask&A_mask)==mask for mask in row)**2 for row in masks)
            assert Q<=a**3
            assert (Q==a**3)==cartesian_coset(g,A)
            eq+=Q==a**3
            if 100*(a**3-Q)<=a**3:
                stability_certificate(g,A,Q);stable+=1
            stats['exhaustive_nonempty_subsets']+=1
        reports.append({'exhaustive_group':mods,'nonempty_subsets':(1<<M)-1,
                        'equality_cases':eq,'stable_cases':stable})
    for mods in ((101,),(101,2)):
        g=Group(mods)
        A={x for x in g.points if x[0]!=0}
        Q=q_count(g,A)
        reports.append(stability_certificate(g,A,Q))
        stats['nonzero_defect_stability_cases']+=1
    g=Group((101,)); a=100
    assert q_count(g,{x for x in g.points if x!=(0,)})==a**3-a**2+a
    # A diagonal subgroup is not a Cartesian subgroup.
    g=Group((5,5));A={(i,i) for i in range(5)}
    assert q_count(g,A)==25 and not cartesian_coset(g,A)
    stats['noncartesian_subgroup_counterexamples']+=1
    for j in range(48):
        g=Group(((2,2),(3,),(2,3))[j%3]);n=2+(j%2);q=2+(j%3)
        weights={(y,x):int(rng.random()<0.66) for y in g.points for x in range(n)}
        phi={(y,x):rng.randrange(q) for y in g.points for x in range(n)}
        verify_arrangement_case(g,n,q,weights,phi,fourier=(j<12))
        stats['random_indicator_arrangement_cases']+=1
        stats['floating_fourier_identity_cases']+=(j<12)
        zero={p:0 for p in phi}
        verify_arrangement_case(g,n,q,weights,zero,constant_label=True)
        stats['constant_label_coupling_cases']+=1
    for j in range(12):
        g=Group((2,2));n=q=2
        weights={(y,x):F(rng.randrange(5),4) for y in g.points for x in range(n)}
        phi={p:rng.randrange(q) for p in weights}
        verify_arrangement_case(g,n,q,weights,phi)
        stats['rational_vertex_weight_cases']+=1
    # Rectangular subgroup model, exact at every moment from d=1 to 8.
    g=Group((4,2));n=q=4
    H={y for y in g.points if y[0]%2==0};J={1,3}
    weights={(y,x):int(y in H and x in J) for y in g.points for x in range(n)}
    phi={p:0 for p in weights}
    R=verify_arrangement_case(g,n,q,weights,phi,fourier=True,constant_label=True)
    for d in range(1,9):
        assert R[d-1]==len(H)**(2*d+1)*len(J)**(2*d-1)
        if d>=2: assert R[d-1]*R[0]**(d-2)==R[1]**(d-1)
    reports.append({'sharp_subgroup_model_R1_to_R8':R})
    stats['exact_subgroup_moment_models']+=1
    stats['floating_fourier_identity_cases']+=1
    # Balance is essential: X x {0} with vertical group of order 3.
    g=Group((2,));n=q=3
    weights={(y,x):int(x==0) for y in g.points for x in range(n)}
    phi={p:0 for p in weights};R=verify_arrangement_case(g,n,q,weights,phi)
    beta=F(1,3);a2=F(R[1],2**5*3**3);a8=F(R[7],2**17*3**15)
    assert a8<a2**7/beta**18
    stats['false_balance_formula_counterexamples']+=1
    # Full-domain label classification for all 2^6 maps Z2 x Z3 -> Z2.
    g=Group((2,3))
    for values in product(range(2),repeat=6):
        verify_labels(g,2,dict(zip(g.points,values)))
        stats['exhaustive_label_maps']+=1
    g=Group((3,3))
    for _ in range(48):
        phi={x:rng.randrange(3) for x in g.points}
        verify_labels(g,3,phi)
        stats['random_label_maps']+=1
    g=Group((4,4))
    for c in range(4):
        f=[rng.randrange(4) for _ in range(4)];h=[rng.randrange(4) for _ in range(4)]
        phi={x:(c*x[0]*x[1]+f[x[0]]+h[x[1]])%4 for x in g.points}
        verify_labels(g,4,phi);stats['multiadditive_label_models']+=1
    # Exhaustive joint-extremizer classification on 8 possible domain points.
    g=Group((2,2));n=q=2
    positions=[(y,x) for y in g.points for x in range(n)]
    joint_equalities=0
    for states in product(range(3),repeat=len(positions)):
        if not any(states): continue
        weights={p:int(state>0) for p,state in zip(positions,states)}
        phi={p:max(0,state-1) for p,state in zip(positions,states)}
        m=make_m(g,n,q,weights,phi);R,_=counts_from_m(m,n,q,3)
        Gamma=sum(sum(weights[(y,x)] for y in g.points)**3 for x in range(n))
        exact=(R[0]==Gamma and R[2]*R[0]==R[1]**2)
        assert exact==joint_normal_form(g,n,q,weights,phi)
        joint_equalities+=exact
        stats['exhaustive_joint_extremizer_cases']+=1
    reports.append({'joint_extremizers_on_Z2_squared_times_Z2':joint_equalities})
    g=Group((3,));n=q=3
    for j in range(180):
        weights={(y,x):1 for y in g.points for x in range(n)}
        if j<90:
            slopes=[rng.randrange(3) for _ in range(3)]
            offsets=[rng.randrange(3) for _ in range(3)]
            phi={(y,x):(slopes[x]*y[0]+offsets[x])%3 for y in g.points for x in range(n)}
        else:
            phi={p:rng.randrange(3) for p in weights}
        m=make_m(g,n,q,weights,phi);R,_=counts_from_m(m,n,q,3)
        exact=(R[0]==81 and R[2]*R[0]==R[1]**2)
        assert exact==joint_normal_form(g,n,q,weights,phi)
        stats['ternary_joint_extremizer_cases']+=1
    # Exact stability of moment interpolation on rational spectra.
    for d in range(3,11):
        for _ in range(40):
            t=[F(rng.randrange(10),rng.randrange(1,6)) for _ in range(8)]
            S1=sum(t);S2=sum(x*x for x in t)
            if not S2: continue
            lam=S2/S1
            gap=sum(x**d for x in t)*S1**(d-2)/S2**(d-1)-1
            variance=sum(x/S1*(x/lam-1)**2 for x in t)
            assert gap>=(d-2)*variance
            for w in t:
                polynomial=sum((d-2-j)*w**j for j in range(d-2))
                assert w**(d-1)-1-(d-1)*(w-1)==(w-1)**2*polynomial
            stats['exact_spectral_stability_cases']+=1
    for k in range(1,13):
        for d in range(2,9):
            e=2*k*4**k;u=8*2**k
            assert 4*e+u<=3*k*4**(k+1)
            assert (3*d-2)*e+(d-1)*u==(6*d-4)*k*4**k+8*(d-1)*2**k
            assert (3*d-2)*4**k < 4*(d-1)*4**k if d>2 else True
            stats['exponent_comparisons']+=1
    result={'status':'PASS','seed':20261006,'counts':dict(stats),'reports':reports,
            'notes':['All count, normalization, and stability assertions use exact arithmetic.',
                     'Fourier cross-checks alone use complex floating point with relative tolerance 1e-9.',
                     'These finite tests are not a proof or a Lean/kernel verification.']}
    out=json.dumps(result,indent=2)
    print(out)
    print(f'Elapsed seconds: {time.perf_counter()-started:.3f}')
    Path(__file__).with_name('verification_results.json').write_text(out+'\n',encoding='utf-8')

if __name__=='__main__':
    main()
