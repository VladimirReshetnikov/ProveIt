#!/usr/bin/env python3
"""Exact interlacing of the rotated Ehrhart polynomials of K_{1^k,n}."""
from functools import lru_cache
from fractions import Fraction
from math import comb, prod
from argparse import ArgumentParser
from sympy import Poly, ZZ, oo, symbols

z = symbols('z')

def choose(n, k):
    return comb(n, k) if 0 <= k <= n else 0

def gamma(r, n, j):
    return choose(2*j, j)*sum(choose(n,l)*choose(r,2*j-l) for l in range(j+1))

def weights(r, n):
    # Coefficients of Q_{n+r-2h} in the rotated Ehrhart polynomial.
    d = n+r
    g = [gamma(r,n,j)*4**(r-j) for j in range(r+1)]
    return [prod(range(d-2*h+1,d+1))*sum(g[j]*choose(j,h) for j in range(h,r+1)) for h in range(r+1)]

def step(p,q,b):
    size = max(len(p)+1,len(q))
    row = [0]*size
    for j,a in enumerate(p): row[j+1] += a
    for j,a in enumerate(q): row[j] -= b*a
    return row

@lru_cache(maxsize=None)
def short(r,n):
    if n < r+1:
        raise ValueError("short coordinates require n >= r+1")
    w = weights(r,n)
    def component(i):
        p = {0:[1-i],-1:[-i]}
        den = {0:1,-1:1}
        for s in range(1,r+1):
            den[s]=1
            p[s]=step(p[s-1],p[s-2],(n+s-1)**2)
        for s in range(-2,-r-1,-1):
            den[s]=den[s+1]*(n+s+1)**2
            p[s]=step(p[s+1],p[s+2],den[s+1]//den[s+2])
        out = [Fraction() for _ in range(r+2)]
        for h,c in enumerate(w):
            s=r-2*h
            for j,b in enumerate(p[s]):
                out[j]+=Fraction(c*b,den[s])
        assert all(x.denominator==1 for x in out)
        return tuple(int(x) for x in out)
    return component(0),component(1)

def differences(seq):
    while seq:
        yield seq[0]
        seq=[b-a for a,b in zip(seq,seq[1:])]

def scalar_polynomial_degrees(r, base):
    # Clearing S=prod_{i=1}^{r-1}(n-i)^2 gives a numerator degree <=7r+2;
    # interpolation plus identity therefore proves degrees <=r (A), <=r+1 (B).
    N=7*r+4
    rows=[short(r,base+i) for i in range(N)]
    for i in (0,1):
        for column in zip(*(ab[i] for ab in rows)):
            assert not any(list(differences(list(column)))[r+i+1:])

def bezout_diagonal(A,B,r):
    # Construct coeffs of (A(u)B(v)-B(u)A(v))/(u-v) using i>j.
    H=[[0]*r for _ in range(r)]
    for i in range(1,r+1):
        for j in range(i):
            c=A[i]*B[j]-A[j]*B[i]
            for s in range(i-j):
                H[i-1-s][j+s]+=c
    ans=[]
    for parity in (0,1):
        ix=list(range(parity,r,2))
        block=[[H[a][b] for b in ix] for a in ix]
        # Bareiss elimination gives successive leading minors as diagonal pivots.
        previous=1
        for h in range(len(ix)):
            pivot=block[h][h]
            ans.append(pivot)
            assert pivot != 0
            for a in range(h+1,len(ix)):
                for b in range(h+1,len(ix)):
                    value=pivot*block[a][b]-block[a][h]*block[h][b]
                    quotient,remainder=divmod(value,previous)
                    assert remainder==0
                    block[a][b]=quotient
            previous=pivot
    return ans

def determinant(A,B,C,D,r):
    co=[0]*(2*r+1)
    for i in range(r+1):
        for j in range(r+2):
            val=A[i]*D[j]-B[i]*C[j]
            if val:
                assert (i+j)%2==0 and i+j<=2*r
                co[i+j]+=val
    return Poly.from_list(co[::2][::-1],z,domain=ZZ)

def positive_poly(f):
    if f.is_zero: return False
    if f.eval(0)<=0: return False
    if all(a>=0 for a in f.all_coeffs()): return True
    return f.count_roots(0,oo)==0

def full(r,n):
    d=r+n
    w=weights(r,n)
    q=[[1],[0,1]]
    for i in range(1,d):
        q.append(step(q[-1],q[-2],i*i))
    out=[0]*(d+1)
    for h,c in enumerate(w):
        if d-2*h<0:
            assert c==0
        else:
            for j,b in enumerate(q[d-2*h]):
                out[j]+=c*b
    return Poly.from_list(out[::-1],z,domain=ZZ)

def euclidean_interlace(P,Q):
    # At each stage the minus remainder must lead positively and lose one degree.
    while Q.degree()>0:
        assert P.LC()>0 and Q.LC()>0 and P.degree()==Q.degree()+1
        R=-P.prem(Q)
        assert R.degree()==Q.degree()-1 and R.LC()>0
        P,Q=Q,R.primitive()[1]
    assert Q.LC()>0

def verify(r):
    base=r+2  # common safe lower endpoint for width r and r+1
    for s in [r,r+1]: scalar_polynomial_degrees(s,base)
    sample_size=(2*r+1)*((r+1)//2)+1
    samples=[bezout_diagonal(*short(r,base+i),r) for i in range(sample_size)]
    for minor in zip(*samples):
        assert all(a>=0 for a in differences(list(minor))) and minor[0]>0
    cross=[determinant(*short(r,base+i),*short(r+1,base+i),r) for i in range(2*r+3)]
    D=list(differences(cross))
    assert positive_poly(D[0]) and all(F.is_zero or positive_poly(F) for F in D)
    for n in range(1,base): euclidean_interlace(full(r+1,n),full(r,n))
    print(f'k={r+1}: {r} leading minors, {len(D)} cross rows, {base-1} small n. PASS',flush=True)

if __name__=='__main__':
    if not __debug__:
        raise RuntimeError('Run with assertions enabled (no -O).')
    ap=ArgumentParser(description=__doc__)
    ap.add_argument('--through',type=int,default=20,help='largest k to verify')
    args=ap.parse_args()
    for r in range(args.through): verify(r)
