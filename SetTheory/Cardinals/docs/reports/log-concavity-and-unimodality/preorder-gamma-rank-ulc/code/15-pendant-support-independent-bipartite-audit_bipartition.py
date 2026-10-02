#!/usr/bin/env python3
"""Independent finite checks for the bipartite directed-support construction.

Direct enumerator deduplicates ordered supports of directed matchings.
Construction enumerator uses Hall tests for the two dummy-basis families.
Integer activity weights include zero. All comparisons and ULC tests are exact.
Selected multivariate Lorentzian tests use exact rational symmetric inertia.
"""
from collections import defaultdict
from fractions import Fraction
from itertools import combinations
import json
import math
from pathlib import Path
import random
import time

OUT = Path(__file__).resolve().parent

def submasks(mask):
    s = mask
    while True:
        yield s
        if s == 0:
            return
        s = (s-1) & mask

def product_weights(mask, w):
    ans = 1
    while mask:
        bit = mask & -mask
        ans *= w[bit.bit_length()-1]
        mask ^= bit
    return ans

def support_weight(S, T, u, v):
    return product_weights(S, u)*product_weights(T, v)

def direct(n, m, plus, minus, u, v):
    """plus[c] permits c -> exterior i; minus[c] permits exterior i -> c."""
    supports = set()
    def rec(c, usedI, S, T):
        if c == n:
            supports.add((S, T))
            return
        rec(c+1, usedI, S, T)
        for i in range(m):
            if (usedI >> i) & 1:
                continue
            if (plus[c] >> i) & 1:
                rec(c+1, usedI | (1<<i), S | (1<<c), T | (1<<(n+i)))
            if (minus[c] >> i) & 1:
                rec(c+1, usedI | (1<<i), S | (1<<(n+i)), T | (1<<c))
    rec(0, 0, 0, 0)
    poly = defaultdict(int)
    for S, T in supports:
        used = S | T
        unusedC = ((1<<n)-1) ^ (used & ((1<<n)-1))
        monomial = unusedC | (used & (((1<<m)-1)<<n))
        poly[monomial] += support_weight(S,T,u,v)
    return {k:v for k,v in poly.items() if v}, supports

def hall(C, I, adj):
    for A in submasks(C):
        neighbors = 0
        for c in range(len(adj)):
            if (A >> c) & 1:
                neighbors |= adj[c]
        if (neighbors & I).bit_count() < A.bit_count():
            return False
    return True

def bases(n,m,adj):
    return [(C,I) for C in range(1<<n) for I in range(1<<m)
            if C.bit_count()==I.bit_count() and hall(C,I,adj)]

def construction(n,m,plus,minus,u,v):
    poly=defaultdict(int)
    for P,R in bases(n,m,plus):
        for Q,L in bases(n,m,minus):
            if (R&L) or (P&Q):
                continue
            # Exterior MAP removes R&L. Core merge removes P&Q,
            # maps both dummies to one unused-core variable, and one to 1.
            unusedC=((1<<n)-1) ^ (P|Q)
            monomial=unusedC | ((R|L)<<n)
            S=P | (L<<n)
            T=Q | (R<<n)
            poly[monomial]+=support_weight(S,T,u,v)
    return {k:v for k,v in poly.items() if v}

def inertia(A):
    """Exact rational congruence elimination, counting positive/negative/zero."""
    A=[[Fraction(x) for x in row] for row in A]
    pos=neg=zero=0
    while A:
        n=len(A)
        diag=next((i for i in range(n) if A[i][i]),None)
        if diag is not None:
            ids=[diag]+[i for i in range(n) if i!=diag]
            A=[[A[i][j] for j in ids] for i in ids]
            p=A[0][0]
            pos+=p>0; neg+=p<0
            A=[[A[i][j]-A[i][0]*A[0][j]/p for j in range(1,n)]
               for i in range(1,n)]
            continue
        pair=next(((i,j) for i in range(n) for j in range(i+1,n) if A[i][j]),None)
        if pair is None:
            zero+=n
            break
        i,j=pair
        ids=[i,j]+[k for k in range(n) if k not in (i,j)]
        A=[[A[i][j] for j in ids] for i in ids]
        b=A[0][1]
        pos+=1; neg+=1
        A=[[A[i][j]-(A[i][0]*A[1][j]+A[i][1]*A[0][j])/b
            for j in range(2,n)] for i in range(2,n)]
    return pos,neg,zero

def check_lorentzian(poly,n,m):
    supp=set(poly)
    N=n+m
    # Symmetric basis exchange, sufficient for squarefree M-convexity.
    for A in supp:
        for B in supp:
            for i in range(N):
                if not ((A & ~B)>>i)&1:
                    continue
                assert any(((B & ~A)>>j)&1 and
                           (A^(1<<i)^(1<<j)) in supp and
                           (B^(1<<j)^(1<<i)) in supp for j in range(N))
    if n<2:
        return 0
    count=0
    for inds in combinations(range(N),n-2):
        D=sum(1<<i for i in inds)
        A=[[0]*N for _ in range(N)]
        for mono,coef in poly.items():
            if mono&D!=D:
                continue
            rem=mono^D
            assert rem.bit_count()==2
            i,j=[i for i in range(N) if rem>>i&1]
            A[i][j]=A[j][i]=coef
        assert inertia(A)[0]<=1
        count+=1
    return count

def check_case(n,m,plus,minus,u,v,full=False):
    p,supports=direct(n,m,plus,minus,u,v)
    q=construction(n,m,plus,minus,u,v)
    assert p==q,(n,m,plus,minus,u,v,p,q)
    assert p.get((1<<n)-1)==1
    assert all(mask.bit_count()==n for mask in p)
    F=[0]*(n+1)
    for mask,a in p.items():
        F[(mask>>n).bit_count()]+=a
    for k in range(1,n):
        assert k*(n-k)*F[k]**2 >= (k+1)*(n-k+1)*F[k-1]*F[k+1]
    return len(supports),check_lorentzian(p,n,m) if full else 0

def graph_from_code(n,m,code):
    plus=[0]*n; minus=[0]*n
    for c in range(n):
        for i in range(m):
            state=code&3; code>>=2
            if state&1: plus[c]|=1<<i
            if state&2: minus[c]|=1<<i
    return plus,minus

def main():
    start=time.monotonic()
    rng=random.Random(202610010919)
    cases=0; support_instances=0; hessians=0
    suites=[]
    for n,m in [(1,1),(1,3),(2,2),(2,3)]:
        count=4**(n*m)
        for code in range(count):
            plus,minus=graph_from_code(n,m,code)
            u=[rng.randrange(4) for _ in range(n+m)]
            v=[rng.randrange(4) for _ in range(n+m)]
            s,h=check_case(n,m,plus,minus,u,v,full=True)
            support_instances+=s; hessians+=h; cases+=1
        suites.append({'type':'exhaustive directed graphs','shore_sizes':[n,m],
                       'graphs':count,'activities':'seeded integers 0..3'})
    for n,m,count in [(3,3,300),(3,4,150),(4,3,150),(4,4,100)]:
        for trial in range(count):
            plus,minus=graph_from_code(n,m,rng.randrange(4**(n*m)))
            u=[rng.randrange(5) for _ in range(n+m)]
            v=[rng.randrange(5) for _ in range(n+m)]
            s,h=check_case(n,m,plus,minus,u,v,full=True)
            support_instances+=s; hessians+=h; cases+=1
        suites.append({'type':'seeded random directed graphs','shore_sizes':[n,m],
                       'graphs':count,'activities':'seeded integers 0..4'})
    # Opposite-arc single edge: orientations are distinct ordered supports.
    p,s=direct(1,1,[1],[1],[2,3],[5,7])
    assert p=={1:1,2:29} and len(s)==3
    # K_2,2 one-way: two perfect matchings have just one full ordered support.
    p,s=direct(2,2,[3,3],[0,0],[1]*4,[1]*4)
    assert p=={3:1,5:1,6:1,9:1,10:1,12:1} and len(s)==6
    # Boundaries: isolates can make actual degree smaller than shore size.
    p,s=direct(3,3,[1,0,0],[0,0,0],[1]*6,[1]*6)
    assert p=={7:1,14:1}
    receipt={'verdict':'PASS','seed':202610010919,'cases':cases,
             'ordered_support_instances':support_instances,
             'exact_quadratic_hessian_inertia_checks':hessians,
             'checks':['exact direct matching-support vs Hall/dummy construction',
                       'unit empty-support coefficient','constant total shore degree',
                       'exact order-shore binomial ULC','symmetric support exchange',
                       'exact rational quadratic Hessian inertia'],
             'suites':suites,'boundary_cases':['opposite arcs counted separately',
                       'multiple matchings counted once per support',
                       'actual degree below shore order'],
             'elapsed_seconds':round(time.monotonic()-start,3)}
    (OUT/'verification.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':
    main()
