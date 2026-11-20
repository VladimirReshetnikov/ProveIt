#!/usr/bin/env python3
"""Exact finite checks for operator norms, analytic identities, and reuse.

Uses only Python's standard library. These are implementation and constant
checks, not universal mathematical proofs or object-iPRA derivations.
"""
from fractions import Fraction as Q
from collections import Counter
import json

counts = Counter()

def check(label, condition):
    assert condition, label
    counts[label] += 1

def norm(v):
    return sum(map(abs, v), Q(0))/len(v)

def col_norm(K):
    return max(sum((abs(row[j]) for row in K), Q(0))/len(K)
               for j in range(len(K[0])))

def apply(K, v):
    return tuple(sum((x*y for x,y in zip(row,v)),Q(0))/len(v) for row in K)

def sub(u,v):
    return tuple(x-y for x,y in zip(u,v))

def neumann(K,g,n):
    total=tuple(Q(0) for _ in g)
    cur=g
    for _ in range(n):
        total=tuple(x+y for x,y in zip(total,cur))
        cur=apply(K,cur)
    return total,cur

def cadd(z,w): return (z[0]+w[0],z[1]+w[1])
def cneg(z): return (-z[0],-z[1])
def csub(z,w): return cadd(z,cneg(w))
def cmul(z,w): return (z[0]*w[0]-z[1]*w[1],z[0]*w[1]+z[1]*w[0])
def cscale(t,z): return (t*z[0],t*z[1])
def cinv(z):
    d=z[0]*z[0]+z[1]*z[1]
    assert d>0
    return (z[0]/d,-z[1]/d)
def cpow(z,n):
    out=(Q(1),Q(0))
    for _ in range(n): out=cmul(out,z)
    return out
def sq(z): return z[0]*z[0]+z[1]*z[1]
ONE=(Q(1),Q(0))
ZERO=(Q(0),Q(0))

# Exact matrix contraction, residual, and perturbation checks.
for level in range(1,5):
    J=2**level
    grid=tuple(Q(2*i+1,2*J) for i in range(J))
    K=tuple(tuple(x*t/2 for t in grid) for x in grid)
    g=tuple(Q(1) for _ in grid)
    q=Q(1,4)
    check('column_norm',col_norm(K)<=q)
    second=sum((t*t for t in grid),Q(0))/J
    c=Q(1,4)/(1-second/2)
    exact=tuple(1+c*x for x in grid)
    check('matrix_solution',sub(exact,g)==apply(K,exact))
    for n in range(0,13):
        y,power=neumann(K,g,n)
        residual=sub(sub(y,g),apply(K,y))
        check('finite_residual',residual==tuple(-x for x in power))
        check('neumann_tail',norm(sub(y,exact))<=q**n/(1-q))
        check('iterate_bound',norm(power)<=q**n)
        for eps in [Q(1,8),Q(1,16)]:
            L=tuple(tuple((Q(1,2)-eps)*x*t for t in grid) for x in grid)
            h=tuple(1-eps/2 for _ in grid)
            z,_=neumann(L,h,n)
            delta=col_norm(tuple(sub(a,b) for a,b in zip(K,L)))
            check('neumann_perturbation',norm(sub(y,z))<=2*norm(sub(g,h))+4*delta)

# A product-L1 kernel norm is not an L1 operator norm.
for m in range(1,7):
    J=2**m
    v=tuple(Q(J) if j==0 else Q(0) for j in range(J))
    K=(v,)
    check('wrong_norm_counterexample',norm(v)==1 and col_norm(K)==J
          and apply(K,v)==(Q(J),))

# Exact moments of dyadic average approximations to 2(1+t)/3.
for level in range(0,8):
    J=2**level
    vals=tuple(Q(2,3)+Q(2*i+1,3*J) for i in range(J))
    for j in range(13):
        a=sum((vals[i]*(Q(i+1,J)**(j+1)-Q(i,J)**(j+1))/(j+1)
               for i in range(J)),Q(0))
        exact=Q(2,3)*(Q(1,j+1)+Q(1,j+2))
        check('moment_error',abs(a-exact)<=Q(1,6*J))
        if j==0: check('moment_mass',a==1)

# Pointwise rational complex identities underlying derivative and tail bounds.
zs=[(Q(1,2),Q(0)),(Q(1,3),Q(1,4)),(Q(-1,4),Q(1,3)),ZERO]
hs=[(Q(1,20),Q(0)),(Q(0),Q(1,20)),(Q(-1,20),Q(1,20))]
r=Q(3,4); b=4
for z in zs:
    for h in hs:
        zh=cadd(z,h)
        check('complex_guard',sq(z)<=r*r and sq(zh)<=r*r)
        for t in [Q(i,8) for i in range(9)]:
            az=csub(ONE,cscale(t,z)); ah=csub(ONE,cscale(t,zh))
            iz=cinv(az); ih=cinv(ah)
            deriv=cscale(t,cmul(iz,iz))
            lhs=csub(csub(ih,iz),cmul(h,deriv))
            rhs=cscale(t*t,cmul(cmul(h,h),cmul(ih,cmul(iz,iz))))
            check('complex_remainder_identity',lhs==rhs)
            check('complex_remainder_bound',sq(lhs)<=b**6*sq(h)**2)
            for N in range(1,9):
                zt=cscale(t,z)
                poly=ZERO
                for j in range(N): poly=cadd(poly,cpow(zt,j))
                tail=cmul(cpow(zt,N),iz)
                check('geometric_identity',csub(iz,poly)==tail)
                check('geometric_bound',sq(tail)<=b*b*r**(2*N))

# The generic block schedule uses rational Bernoulli, not a logarithm oracle.
for b0 in range(2,12):
    q=Q(b0-1,b0)
    check('block_contraction',q**b0<=Q(1,2))
    for R in range(6):
        check('block_schedule',q**(b0*R)<=Q(1,2)**R)

# Reverse sensitivity on a graph with a shared root and cancellation-free bounds.
edges=[[],[(0,Q(2))],[(0,Q(3))],[(1,Q(1)),(2,Q(1))]]
weight=[Q(0) for _ in edges];weight[3]=1
for v in reversed(range(len(edges))):
    for u,L in edges[v]: weight[u]+=weight[v]*L
check('shared_weight',weight==[Q(5),Q(1),Q(1),Q(1)])
for eta in [(Q(1,16),Q(1,32),Q(1,64),Q(0)),(Q(0),Q(1,4),Q(1,3),Q(1,7))]:
    errors=[]
    for v in range(len(edges)):
        errors.append(eta[v]+sum((L*errors[u] for u,L in edges[v]),Q(0)))
    check('reverse_budget',errors[3]==sum((w*e for w,e in zip(weight,eta)),Q(0)))

print(json.dumps({'status':'passed','arithmetic':'exact rational pairs; no floating-point checks',
 'counts':dict(counts),'total_assertions':sum(counts.values()),
 'scope':'Finite implementation checks, not universal proofs or object-iPRA derivations.'},indent=2))
