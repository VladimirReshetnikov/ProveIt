"""Exact, independent finite-cutoff verification of regular trigamma moments.

The first route uses ordinary Faulhaber summation of finite cutoffs.  The
second uses the new Bernoulli recurrence.  Multiple zeta values are retained
as formal symbols; no numerical recognition or numerical independence is used.
"""
from functools import lru_cache
from pathlib import Path
import json
import sympy as s

N = s.Symbol('N')
gamma = s.Symbol('EulerGamma')

def B(k):
    return s.bernoulli(k, 0)

@lru_cache(None)
def compositions(n):
    if n == 0:
        return ((),)
    return tuple((k,)+rest for k in range(1,n+1)
                 for rest in compositions(n-k))

def Z(word):
    if not word:
        return s.S.One
    return s.Symbol('Z_'+'_'.join(map(str,word)))

@lru_cache(None)
def boundary(d, k):
    if d == 0:
        return s.S.One if k == 0 else s.S.Zero
    if k < d:
        return s.S.Zero
    if d == 1:
        return B(k-1)
    return sum(B(j-1)*boundary(d-1,k-j) for j in range(1,k-d+2))

@lru_cache(None)
def faulhaber(m):
    p=s.Poly(s.expand((s.bernoulli(m+1,N+1)-s.bernoulli(m+1,1))/(m+1)),N)
    return tuple((k[0],v) for k,v in p.terms())

@lru_cache(None)
def T(d,m):
    """Constant coefficient of sum(k=1..N) k^m zeta(2,k+1)^d."""
    if d==0:
        return s.S.Zero if m>=0 else gamma if m==-1 else Z((-m,))
    if m<0:
        ans=0
        for c in compositions(d):
            mult=s.factorial(d)/s.prod(s.factorial(x) for x in c)
            ans += mult*Z(tuple(2*x for x in c)+(-m,))
        return ans
    f=faulhaber(m)
    ans=sum(v*boundary(d,k) for k,v in f)
    for j in range(1,d+1):
        ans+=s.binomial(d,j)*(sum(v*T(d-j,k-2*j) for k,v in f)
                             -T(d-j,m-2*j))
    return s.expand(ans)

@lru_cache(None)
def C(d,k):
    return s.expand(boundary(d,k)+sum(s.binomial(d,j)*T(d-j,k-2*j)
                                        for j in range(1,d+1)))

@lru_cache(None)
def M(d,m):
    """Centered regular moment with exponent m, where m == d (mod 2)."""
    assert m>=0 and (d-m)%2==0
    p=s.Poly(s.expand((s.bernoulli(m+1,N+s.Rational(1,2))
                      -s.bernoulli(m+1,s.Rational(1,2)))/(m+1)),N)
    return s.expand(sum(v*C(d,k[0]) for k,v in p.terms()))

def anchor(d,k):
    """Independent minimum-index composition formula for k<=1."""
    assert k<=1 and not (d==1 and k==1)
    ans=0
    for c in compositions(d):
        mult=s.factorial(d)/s.prod(s.factorial(x) for x in c)
        word=tuple(2*x for x in c[:-1])+(2*c[-1]-k,)
        ans+=mult*Z(word)
    return s.expand(ans)

def recurrence_C(d,k):
    assert k>=2 and (d+1-k)%2==0
    m=k-2
    if d==1:
        first=0
    else:
        first=d*sum(s.binomial(m,j)*s.Rational(1,2)**j*M(d-1,m-j)
                    for j in range(0,m+1,2))
    if k==2:
        first-=s.Rational(d,2)*(anchor(d-1,0) if d>1 else 1)
    ans=first
    for j in range(1,(d-1)//2+1):
        h=k-4*j
        lower=anchor(d-2*j,h) if h<=0 else C(d-2*j,h)
        ans-=s.binomial(d,2*j)*B(2*j)*lower
    return s.expand(ans)

def main():
    checks=[]
    for d in range(1,9):
        for k in range(2,23):
            if (d+1-k)%2: continue
            residual=s.expand(C(d,k)-recurrence_C(d,k))
            # The formal single-zeta values at even integers satisfy Euler's
            # rational Bernoulli evaluations; finite sums can produce them.
            if residual!=0:
                raise AssertionError((d,k,residual))
            checks.append(['recurrence',d,k])
        for k in range(-6,1):
            assert s.expand(C(d,k)-anchor(d,k))==0,(d,k)
            checks.append(['minimum_index',d,k])
        for k in range(d+1,25,2):
            v=boundary(d,k)+s.Rational(d,2)*boundary(d-1,k-2)
            v+=sum(s.binomial(d,2*j)*B(2*j)*boundary(d-2*j,k-4*j)
                   for j in range(1,d//2+1))
            assert v==0,(d,k,v)
            checks.append(['boundary_cancellation',d,k])
    rows={str(d):{str(m):str(M(d,m)) for m in range(d%2,14,2)}
          for d in range(1,9)}
    result={'status':'PASS','exact_checks':len(checks),'checks':checks,
            'moments':rows,'method':'Faulhaber finite cutoffs versus Bernoulli recurrence; formal MZV words'}
    Path(__file__).with_name('allpowers_exact.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PASS',len(checks),'exact checks')
    for d in (5,6):
        for m in range(d%2,min(7,d),2): print('M',d,m,'=',M(d,m))

if __name__=='__main__':
    main()
