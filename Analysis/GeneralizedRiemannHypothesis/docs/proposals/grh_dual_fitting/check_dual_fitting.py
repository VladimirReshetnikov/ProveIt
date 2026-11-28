#!/usr/bin/env python3
"""Exact finite regression models; not a substitute for the paper proofs."""
from itertools import product
from random import Random
from fractions import Fraction

rng = Random(284711)

def dot(a, b, q):
    return sum(x*y for x,y in zip(a,b)) % q

def span(gens, q, n):
    S = {(0,)*n}
    for g in gens:
        S = {tuple((x+c*y)%q for x,y in zip(v,g)) for v in S for c in range(q)}
    return S

def ann(S, q, n):
    return {v for v in product(range(q), repeat=n) if all(dot(v,w,q)==0 for w in S)}

def length(size, ell):
    n=0
    while size>1 and size%ell==0:
        n+=1; size//=ell
    assert size==1
    return n

def valuation(x, ell):
    if x==0: return float('inf')
    x=abs(x); k=0
    while x%ell==0: x//=ell; k+=1
    return k

def det(A):
    A=[list(map(Fraction,row)) for row in A]; d=Fraction(1)
    for i in range(len(A)):
        j=next((j for j in range(i,len(A)) if A[j][i]),None)
        if j is None: return 0
        if j!=i: A[i],A[j]=A[j],A[i]; d=-d
        a=A[i][i]; d*=a
        for j in range(i+1,len(A)):
            c=A[j][i]/a
            for k in range(i+1,len(A)): A[j][k]-=c*A[i][k]
            A[j][i]=0
    assert d.denominator==1
    return int(d)

# Relative length: L is the relation lattice modulo p, D = L^perp.
# U is inverse image of an arbitrary V under evaluation. L' = U^perp.
count=noninj=outside=0
for ell,h in [(2,1),(2,2),(2,3),(3,2)]:
    q=ell**h
    for _ in range(25):
        n=rng.choice([1,2,3] if q<=4 else [1,2]); m=rng.choice([1,2,3] if q<=4 else [1,2])
        randvec=lambda n: tuple(rng.randrange(q) for _ in range(n))
        L=span([randvec(n) for _ in range(rng.randrange(n+1))],q,n)
        D=ann(L,q,n)
        assert ann(D,q,n)==L
        z=[randvec(n) for _ in range(m)]
        ev=lambda w: tuple(dot(w,g,q) for g in z)
        Z={ev(w) for w in D}
        V=span([randvec(m) for _ in range(rng.randrange(m+1))],q,m)
        U={w for w in D if ev(w) in V}
        Lp=ann(U,q,n)
        assert L<=Lp and ann(Lp,q,n)==U
        a=length(len(Z)//len(Z&V),ell)
        assert a==length(len(D)//len(U),ell)==length(len(Lp)//len(L),ell)
        noninj+=len(Z)<len(D); outside+=not V<=Z; count+=1
assert noninj and outside
print(f'Relative duality: {count} exact cases ({noninj} noninjective evaluations, {outside} V not contained in Z).')

# Full-rank triangular relation matrices with pI in their row lattice.
# Generate unimodular row/column operations on diag(ell**a_i).
count=0
for ell,h in [(2,2),(2,3),(3,2)]:
    q=ell**h
    for _ in range(30):
        n=rng.choice([1,2,3] if q<=4 else [1,2])
        aa=[rng.randrange(h+1) for _ in range(n)]
        B=[[ell**aa[i] if i==j else 0 for j in range(n)] for i in range(n)]
        for _ in range(4):
            if n>1:
                i,j=rng.sample(range(n),2); k=rng.choice([-2,-1,1,2])
                if rng.randrange(2): B[i]=[x+k*y for x,y in zip(B[i],B[j])]
                else:
                    for row in B: row[i]+=k*row[j]
        Z={u for u in product(range(q),repeat=n) if all(dot(row,u,q)==0 for row in B)}
        d=valuation(det(B),ell)
        assert d==sum(aa)==length(len(Z),ell)
        for c in range(h+2):
            Zc={u for u in Z if all(ell**c*x%q==0 for x in u)}
            assert length(len(Zc),ell)==sum(min(a,c) for a in aa)
            assert d<=length(len(Z)//len(Zc),ell)+n*min(c,h)
        count+=1
print(f'Specialization: {count} exact lattice cases, with all tested C-torsion bounds.')

# Alternation inclusion: N = lattice with diagonal relation exponents.
# Choose w_i of arbitrary finite order in quotient. Any determinant formed
# from rows of N + span(w_i) multiplied by product of their orders belongs
# to original determinant ideal. Work with R evaluated at integer values;
# this tests the numerical identity underlying the polynomial expansion.
count=0
for ell in [2,3,5]:
    for _ in range(100):
        n=rng.randint(1,4); aa=[rng.randint(0,5) for _ in range(n)]
        ws=[[rng.randint(-10,10) for _ in range(n)] for _ in range(rng.randint(0,5))]
        costs=[max(0,max(a-valuation(x,ell) for a,x in zip(aa,w))) for w in ws]
        rows=[]
        for i in range(n):
            row=[rng.randint(-3,3)*ell**a for a in aa]
            for w in ws:
                c=rng.randint(-4,4); row=[x+c*y for x,y in zip(row,w)]
            rows.append(row)
        assert valuation(det(rows),ell)+sum(costs)>=sum(aa)
        count+=1
print(f'Alternating determinant cost: {count} exact integer matrix cases.')

# Row packing: matrix-unit products isolate rows of d x (s*d) generators.
count=0
for d,s in [(1,3),(2,2),(3,2)]:
    for _ in range(30):
        n=d*s; H=[[[rng.randint(-5,5) for _ in range(n)] for _ in range(d)] for _ in range(3)]
        coeff=[[[rng.randint(-3,3) for _ in range(d)] for _ in H] for _ in range(d)]
        expected=[[sum(coeff[a][k][b]*H[k][b][j] for k in range(len(H)) for b in range(d)) for j in range(n)] for a in range(d)]
        packed=[[0]*n for _ in range(d)]
        for a in range(d):
            for k in range(len(H)):
                for b in range(d):
                    # E_ab times H[k] places row b in row a, zeros elsewhere.
                    unit=[[int(i==a and j==b) for j in range(d)] for i in range(d)]
                    term=[[sum(unit[i][r]*H[k][r][j] for r in range(d)) for j in range(n)] for i in range(d)]
                    for i in range(d):
                        for j in range(n): packed[i][j]+=coeff[a][k][b]*term[i][j]
        assert packed==expected; count+=1
print(f'Matrix-unit row packing: {count} exact block cases.')

# Block finite-length formula, including deficient rank.
count=0
for ell,h in [(2,2),(2,3),(3,1)]:
    q=ell**h
    for aa in product([0,1,h,h+1,None],repeat=3):
        # None is a missing rank, so its relation row is zero.
        diag=[0 if a is None else ell**a for a in aa]
        sols=sum(all(a*x%q==0 for a,x in zip(diag,u)) for u in product(range(q),repeat=3))
        truncated=sum(h if a is None else min(a,h) for a in aa)
        assert length(sols,ell)==truncated
        if truncated<h:
            assert all(a is not None and a<h for a in aa)
            assert truncated==sum(aa)
        count+=1
print(f'Block solution-length formula: {count} diagonal cases, including missing rank.')
# Strict cutoff counterexample and zero-dimensional case.
for ell in [2,3,5]:
    for h in [1,2,3]:
        q=ell**h
        assert length(sum(ell**(h+1)*u%q==0 for u in range(q)),ell)==h
        assert valuation(ell**(h+1),ell)>h
assert det([])==1
print('Strict cutoff counterexamples: 9; empty determinant convention checked.')
print('All exact finite regressions passed.')
