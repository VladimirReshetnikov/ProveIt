"""Exact rational research routines. See article.tex for conventions and proofs.

MZV words use descending indices. No numerical period-independence assumption
is used. The compiler accepts integer orders at least two.
"""
import sympy as S
from functools import lru_cache
from math import factorial
N=S.symbols('N')
G=S.Symbol('EulerGamma')

@lru_cache(None)
def Z(w):
    if not w:return S.Integer(1)
    if w[0]<2 or any(x<1 for x in w):raise ValueError(w)
    return S.Symbol('Z_'+'_'.join(map(str,w)))

@lru_cache(None)
def hz_coeff(q,h):
    # coefficient of N^-h in zeta(q,N), q>=2
    if h==q-1:return S.Rational(1,q-1)
    if h==q:return S.Rational(1,2)
    j=h-q+1
    if j>=2 and j%2==0:return S.bernoulli(j)*S.rf(q,j-1)/S.factorial(j)
    return S.Integer(0)

@lru_cache(None)
def A(w,h):
    # H_{N-1}(w) coefficient of N^-h (w has indices >=2)
    if h==0:return Z(w)
    if not w:return S.Integer(0)
    return S.expand(-sum(A(w[1:],r)*hz_coeff(w[0]+r,h) for r in range(max(0,h-w[0]+2))))

@lru_cache(None)
def P(r):
    return S.Poly(S.expand((S.bernoulli(r+1,N+1)-S.bernoulli(r+1,1))/S.Integer(r+1)),N)

def CTpoly(poly,w):
    return S.expand(sum(c*A(w,h[0]) for h,c in S.Poly(poly,N).terms()))

@lru_cache(None)
def C(w):
    if not w:return S.Integer(1)
    s,v=w[0],w[1:]
    if s>=2:return Z(w)
    if s==1:
        return S.expand(G*Z(v)-sum(Z(v[:j]+(1,)+v[j:]) for j in range(1,len(v)+1))-sum(Z(v[:j]+(v[j]+1,)+v[j+1:]) for j in range(len(v))))
    r=-s
    if not v:return P(r).as_expr().subs(N,-1)
    a=S.expand(CTpoly(P(r).as_expr().subs(N,N-1),v))
    return S.expand(a-sum(c*C((v[0]-h[0],)+v[1:]) for h,c in P(r).terms()))

@lru_cache(None)
def comps(n):
    if n==0:return ((),)
    return tuple((r,)+w for r in range(1,n+1) for w in comps(n-r))

def moment(d,m):
    F=S.Poly(S.expand((S.bernoulli(m+1,N+S.Rational(1,2))-S.bernoulli(m+1,S.Rational(1,2)))/S.Integer(m+1)),N)
    out=0
    for j in range(1,d+1):
      for rs in comps(j):
        w=tuple(2*r for r in rs)
        coeff=(-1)**j*S.binomial(d,j)*Z((2,))**(d-j)*S.factorial(j)/S.prod(S.factorial(r) for r in rs)
        out+=coeff*(CTpoly(F.as_expr(),w)-sum(c*C((w[0]-h[0],)+w[1:]) for h,c in F.terms()))
    return S.expand(out)

@lru_cache(None)
def stuffle(u,v):
    from collections import Counter
    if not u:return {v:1}
    if not v:return {u:1}
    out=Counter()
    for w,c in stuffle(u[1:],v).items():out[(u[0],)+w]+=c
    for w,c in stuffle(u,v[1:]).items():out[(v[0],)+w]+=c
    for w,c in stuffle(u[1:],v[1:]).items():out[(u[0]+v[0],)+w]+=c
    return dict(out)

def linearize(expr):
    from collections import Counter
    out=S.Integer(0)
    for term in S.Add.make_args(S.expand(expr)):
      facs=S.Mul.make_args(term)
      coeff=S.Integer(1); zdict={():1}
      for fac in facs:
        base,exp=fac.as_base_exp()
        if base.is_Symbol and str(base).startswith('Z_'):
          w=tuple(map(int,str(base)[2:].split('_')))
          if not exp.is_Integer or exp<0:raise ValueError('MZV products must have nonnegative integer exponents')
          for _ in range(int(exp)):
            new=Counter()
            for u,c in zdict.items():
              for v,b in stuffle(u,w).items():new[v]+=c*b
            zdict=dict(new)
        else: coeff*=fac
      out+=coeff*sum(c*Z(w) for w,c in zdict.items())
    return S.expand(out)

def tail_words(ps):
    out={():S.Integer(1)}
    for p in ps:
      new={}
      for w,c in out.items():
        new[w]=new.get(w,0)+c*Z((p,))
        for v,mult in stuffle(w,(p,)).items():
          new[v]=new.get(v,0)-c*mult
      out={w:S.expand(c) for w,c in new.items() if c!=0}
    return out

def mixed_moment(ps,m):
    if not ps or any(not isinstance(p,int) or p<2 for p in ps):
        raise ValueError("Tail orders must be a nonempty tuple of integers >= 2.")
    if not isinstance(m,int) or m<0 or (m-sum(p-1 for p in ps))%2:
        raise ValueError("m must be nonnegative and have regular parity.")
    F=S.Poly(S.expand((S.bernoulli(m+1,N+S.Rational(1,2))-S.bernoulli(m+1,S.Rational(1,2)))/S.Integer(m+1)),N)
    out=0
    for w,coeff in tail_words(tuple(ps)).items():
      if w:
       out+=coeff*(CTpoly(F.as_expr(),w)-sum(c*C((w[0]-h[0],)+w[1:]) for h,c in F.terms()))
    return S.expand(out)
