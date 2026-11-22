#!/usr/bin/env python3
"""Exact-rational regression checks for the accompanying human proofs.
These checks are examples, not universal proofs and not object-iPRA checking.
"""
from fractions import Fraction as Q
from itertools import combinations, product
from collections import Counter
import json

counts=Counter()
def check(condition, family):
    assert condition, family
    counts[family]+=1

def norm(p,f):
    return sum((w*abs(x) for w,x in zip(p,f)),Q(0))
def mul(K,f):
    return [sum((a*b for a,b in zip(row,f)),Q(0)) for row in K]
def marginal(p,K):
    return [sum((p[i]*K[i][j] for i in range(len(p))),Q(0))
            for j in range(len(K[0]))]
def kmul(K,L):
    return [[sum((K[i][j]*L[j][k] for j in range(len(L))),Q(0))
             for k in range(len(L[0]))] for i in range(len(K))]

rvals=[Q(0),Q(1,2),Q(1)]
kernels=[[[a,1-a],[b,1-b]] for a,b in product(rvals,repeat=2)]
for p0 in [Q(0),Q(1,3),Q(1)]:
    p=[p0,1-p0]
    for K in kernels:
        q=marginal(p,K)
        for f in product(map(Q,range(-2,3)),repeat=2):
            check(norm(p,mul(K,f))<=norm(q,f),'kernel_contraction')
        for L in kernels:
            KL=kmul(K,L)
            check(marginal(q,L)==marginal(p,KL),'kernel_marginal_composition')
            for f in [(Q(-2),Q(3)),(Q(1),Q(1))]:
                check(mul(KL,f)==mul(K,mul(L,f)),'kernel_functor')

vals=[Q(i,4) for i in range(5)]
for x,y,u,v in product(vals,repeat=4):
    for fun in [min,max,lambda a,b:a*b,lambda a,b:max(a-b,Q(0))]:
        check(abs(fun(x,y)-fun(u,v))<=abs(x-u)+abs(y-v),'connective_sensitivity')

for m in range(1,9):
    n=2**m
    entries=[Q(int(i==j)) for i in range(n) for j in range(n)]
    check(sum(entries,Q(0))/n**2==Q(1,n),'diagonal_small_L1')
    check(sum((entries[i*n+i] for i in range(n)),Q(0))/n==1,'diagonal_large_pullback')
    check(Q(1,n)<=Q(1,2),'supremum_counterexample')

# Exact integral of a one-dimensional triangular Lipschitz bump.
def triangle_integral(c,rad,L):
    knots=sorted(set([Q(0),Q(1)]+[x for x in [c-rad,c,c+rad] if 0<x<1]))
    f=lambda x:L*max(Q(0),rad-abs(x-c))
    return sum(((b-a)*(f(a)+f(b))/2 for a,b in zip(knots,knots[1:])),Q(0))
for c,rad,L in product([Q(0),Q(1,3),Q(1,2),Q(1)],
                       [Q(1,8),Q(1,3),Q(1)], [Q(1),Q(3)]):
    integral=triangle_integral(c,rad,L)
    maxvalue=L*rad
    for delta in [Q(1),Q(1,2),Q(1,4),Q(1,8)]:
        check(maxvalue<=integral/delta+2*L*delta,'L1_uniform_upgrade_1D')

# Chains are sets of simplices; symmetric difference is F_2 addition.
def simplex(vs):
    return tuple(sorted(vs)) if len(set(vs))==len(vs) else None
def addterm(out,s):
    if s is None:return
    if s in out:out.remove(s)
    else:out.add(s)
def boundary(c):
    out=set()
    for s in c:
        if len(s)<=1:continue
        for i in range(len(s)):
            addterm(out,s[:i]+s[i+1:])
    return out

def cmap(c,f):
    out=set()
    for s in c:addterm(out,simplex([f[v] for v in s]))
    return out

def prism(c,f,g):
    out=set()
    for s in c:
        for i in range(len(s)):
            addterm(out,simplex([f[v] for v in s[:i+1]]+[g[v] for v in s[i:]]))
    return out

def allsim(n):
    return [s for k in range(1,n+1) for s in combinations(range(n),k)]
def diameter(s,table):
    return max((table[i][j] for i in s for j in s),default=Q(0))
def metric(points):return [[abs(a-b) for b in points] for a in points]

# All source simplices through dimension 3, and arbitrary maps into 3 vertices.
# Target is the full simplex, so every pair is contiguous, including degeneracies.
for n in range(1,5):
    sims=allsim(n)
    for s in sims:
        check(not boundary(boundary({s})),'boundary_squared')
    maps=list(product(range(3),repeat=n))
    for f,g in product(maps,repeat=2):
        for s in sims:
            c={s}
            check(boundary(prism(c,f,g))^prism(boundary(c),f,g)
                  ==cmap(c,f)^cmap(c,g),'prism_identity')

instances=[
([Q(0),Q(1,2),Q(1)],[Q(0),Q(1,3),Q(2,3),Q(1)],Q(1,3)),
([Q(0),Q(1,3),Q(2,3),Q(1)],[Q(0),Q(2,5),Q(4,5),Q(1)],Q(1,4)),
([Q(0),Q(1)],[Q(0),Q(1,2),Q(1)],Q(1,2))]
for A,B,delta in instances:
    da,db=metric(A),metric(B)
    R=[(i,j) for i,a in enumerate(A) for j,b in enumerate(B) if abs(a-b)<=delta]
    rows=[[j for i0,j in R if i0==i] for i in range(len(A))]
    cols=[[i for i,j0 in R if j0==j] for j in range(len(B))]
    assert all(rows) and all(cols)
    eta=2*delta
    for (i,j),(ii,jj) in product(R,repeat=2):
        check(abs(da[i][ii]-db[j][jj])<=eta,'correspondence_distortion')
    f=[min(row) for row in rows];fp=[max(row) for row in rows]
    g=[min(col) for col in cols];gf=[g[j] for j in f]
    scales=sorted(set([Q(0)]+[x for row in da for x in row]))
    for r in scales:
        for s in allsim(len(A)):
            if diameter(s,da)>r:continue
            check(diameter({f[i] for i in s},db)<=r+eta,'rips_map')
            check(diameter(set(s)|{gf[i] for i in s},da)<=r+2*eta,'rips_composite_contiguity')
            check(diameter({f[i] for i in s}|{fp[i] for i in s},db)<=r+eta,'rips_selection_independence')
            P=prism({s},gf,list(range(len(A))))
            check(all(diameter(t,da)<=r+2*eta for t in P),'rips_prism_validity')
    # Approximate edge tables with opposite signed errors, not assumed metrics.
    eta1,eta2=Q(1,10),Q(1,7)
    dt=[[max(Q(0),da[i][j]+(-1 if (i+j)%2 else 1)*eta1) if i!=j else Q(0)
         for j in range(len(A))] for i in range(len(A))]
    du=[[max(Q(0),da[i][j]-(-1 if (i+j)%2 else 1)*eta2) if i!=j else Q(0)
         for j in range(len(A))] for i in range(len(A))]
    for r in [Q(k,10) for k in range(1,16)]:
        for s in allsim(len(A)):
            exact=diameter(s,da); approx=diameter(s,dt); other=diameter(s,du)
            check(not(exact<=r-eta1) or approx<=r,'scale_lower_inclusion')
            check(not(approx<=r) or exact<=r+eta1,'scale_upper_inclusion')
            check(not(approx<=r) or other<=r+eta1+eta2,'approximate_table_interleaving')

print(json.dumps({'status':'passed','arithmetic':'fractions.Fraction exact',
                  'counts':dict(counts),'total_assertions':sum(counts.values()),
                  'meaning':'Finite regression examples; not a universal proof or Prf PRAAx check.'},indent=2))
