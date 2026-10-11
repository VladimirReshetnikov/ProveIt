from functools import lru_cache
from itertools import product
import sympy as s

GAMMA=s.Symbol('gamma')
def mzv(indices):
    return s.Symbol('Z_'+'_'.join(map(str,indices)))

@lru_cache(None)
def compositions(n):
    if n==0:return ((),)
    return tuple((k,)+tail for k in range(1,n+1) for tail in compositions(n-k))

def B(n):
    return s.bernoulli(n,0)

@lru_cache(None)
def boundary(d,k):
    # coefficient of N^{-k} in zeta(2,N+1)^d
    if d==0:return s.Integer(k==0)
    if k<d:return s.S.Zero
    return sum(B(i-1)*boundary(d-1,k-i) for i in range(1,k+1))

@lru_cache(None)
def tail(d,m):
    # CT sum_{k=1}^N k^m A_k^d, A_k=zeta(2)-H_k^(2)
    if d==0:
        if m>=0:return s.S.Zero
        if m==-1:return GAMMA
        return mzv((-m,))
    if m<0:
        return sum(s.factorial(d)/s.prod(s.factorial(c) for c in cs)*mzv(tuple(2*c for c in cs)+(-m,)) for cs in compositions(d))
    N=s.Symbol('N')
    F=s.Poly(s.expand((s.bernoulli(m+1,N+1)-s.bernoulli(m+1,1))/(m+1)),N)
    Fprev=s.Poly(s.expand(F.as_expr().subs(N,N-1)),N)
    ans=sum(coef*boundary(d,pow[0]) for pow,coef in F.terms())
    for h in range(1,d+1):
        for (a,),coef in Fprev.terms():
            ans+=s.binomial(d,h)*coef*tail(d-h,a-2*h)
    return s.expand(ans)

@lru_cache(None)
def coordinate(d,j):
    # monomial power sum exponent j; CT [sum difference plus boundary]
    ans=boundary(d,j)
    for h in range(1,d+1):
        ans+=s.binomial(d,h)*tail(d-h,j-2*h)
    return s.expand(ans)

def centered(d,k):
    # k-th centered moment, parity equal to d
    N=s.Symbol('N')
    F=s.Poly(s.expand((s.bernoulli(k+1,N+s.Rational(1,2))-s.bernoulli(k+1,s.Rational(1,2)))/(k+1)),N)
    return s.expand(sum(coef*coordinate(d,j[0]) for j,coef in F.terms()))

if __name__=='__main__':
    for j in range(6):print('D',j,coordinate(4,2*j+1))
    for r in range(6):print('V',r,centered(4,2*r))
