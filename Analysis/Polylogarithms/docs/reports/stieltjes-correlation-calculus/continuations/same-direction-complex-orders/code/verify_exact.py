#!/usr/bin/env python3
"""Exact finite checks for the accompanying article.

These checks are not a proof assistant and do not certify analytic limits.
Run from any working directory. Dependencies: sympy.
"""
from __future__ import annotations
import json
from functools import lru_cache
from collections import defaultdict
from pathlib import Path
import sympy as S

ROOT = Path(__file__).resolve().parents[1]
x, q, p, s, h = S.symbols('x q p s h')
counts: dict[str, int] = defaultdict(int)

def check(label: str, difference: S.Expr) -> None:
    assert S.cancel(S.expand(difference)) == 0, (label, difference)
    counts[label] += 1

@lru_cache(None)
def Dneg(k: int, a: S.Expr = q) -> S.Expr:
    """D_{-k}(a). The Bernoulli polynomial is evaluated at 1, not 0."""
    return -(S.bernoulli(k+1,a)-S.bernoulli(k+1,1))/S.Integer(k+1)

@lru_cache(None)
def faulhaber(m: int) -> S.Poly:
    return S.Poly((S.bernoulli(m+1,x)-S.bernoulli(m+1,1))/S.Integer(m+1),x)

@lru_cache(None)
def Cneg(r: int, m: int, a: S.Expr = q) -> S.Expr:
    return S.expand(-sum(c*Dneg(r+k[0],a) for k,c in faulhaber(m).terms()))

@lru_cache(None)
def negpoly(m: int) -> S.Expr:
    f=x
    for _ in range(m):
        f=S.expand(x*(1-x)*S.diff(f,x))
    return f

@lru_cache(None)
def closure_poly(N: int, b: int, m: int) -> S.Expr:
    assert N>=1 and -1<=b<=N-1 and m>=0
    return S.expand(sum(c*S.rf(p,b+j[0])*S.rf(1-p,N-b-1)/S.factorial(N+j[0]-1)
                        for j,c in S.Poly(negpoly(m),x).terms()))

def Eneg(k: int) -> S.Expr:
    # E(-k) = -k zeta(1-k), filled in at k=0.
    return S.Integer(1) if k==0 else -k*S.zeta(1-k)

def beta_int(A:int,B:int) -> S.Expr:
    return S.factorial(A-1)*S.factorial(B-1)/S.factorial(A+B-1)

def comps(n:int):
    if n==0:
        yield ()
    else:
        for j in range(1,n+1):
            for tail in comps(n-j):
                yield (j,)+tail

def Dmoment(m:int) -> dict[tuple[int,tuple[int,...]],S.Expr]:
    """D_m(s); key is (outer-order shift from s, inner index tuple)."""
    out=defaultdict(lambda:S.Integer(0))
    for v in range(m//2+1):
        cv=S.Integer(1) if v==0 else 2*(1-S.Rational(2)**(1-2*v))*S.Symbol(f'zeta_{2*v}')
        for j in range(m-2*v+1):
            d=m-2*v-j
            out[(j-1,(1,)*d)]+=cv*S.rf(s-1,j)/S.factorial(j)*(-1)**d
    for alpha in comps(m):
        out[(-1,alpha)]-=(-1)**m
    return {k:S.expand(v) for k,v in out.items() if S.expand(v)!=0}

def run() -> None:
    # Connected-coordinate polynomial symmetry, shift, and integer interpolation.
    for r in range(6):
        for m in range(6):
            C=Cneg(r,m)
            check('connected_symmetry',C+Cneg(m,r)-Dneg(r)*Dneg(m)-Dneg(r+m))
            check('connected_shift',C.subs(q,q+1)-C+q**r*Dneg(m))
            for L in (1,2,3,5,8):
                direct=sum(S.Integer(j)**r*S.Integer(k)**m for j in range(1,L) for k in range(1,j))
                check('connected_integer_interpolation',C.subs(q,L)-direct)
    # Check the kernel at integer shifts directly as a rational function.
    X,Y=S.symbols('X Y')
    for L in range(1,9):
        B=X**2*Y/((1-X*Y)*(1-X))+(X*Y)**L/((1-X*Y)*(1-Y))-X**L*Y/((1-X)*(1-Y))
        direct=sum(X**j*Y**k for j in range(1,L) for k in range(1,j))
        check('connected_kernel_integer_shift',B-direct)
    # Euler/Newton coefficients at nonpositive and positive integer orders.
    for m in range(9):
        P=S.Poly(negpoly(m),x)
        for n in range(1,14):
            A=sum((-1)**(k+1)*S.binomial(n-1,k-1)*S.Integer(k)**m for k in range(1,n+1))
            check('newton_negative_orders',A-P.coeff_monomial(x**n))
    for n in range(1,11):
        coeff=[S.Integer(1)]+[S.Integer(0)]*4
        for k in range(1,n+1):
            old=coeff[:]
            coeff=[sum(old[i]/S.Integer(k)**(j-i) for i in range(j+1)) for j in range(5)]
        for m in range(1,6):
            A=sum((-1)**(k+1)*S.binomial(n-1,k-1)/S.Integer(k)**m for k in range(1,n+1))
            check('newton_harmonic_orders',A-coeff[m-1]/n)
    # A genuinely independent rational beta evaluation tests the closure polynomial.
    for N in range(1,5):
        for b in range(-1,N):
            for m in range(5):
                Hp=S.Poly(closure_poly(N,b,m),p)
                for n in range(5):
                    rhs=sum(c*Eneg(n+d[0]) for d,c in Hp.terms())
                    product=S.Poly(S.expand(negpoly(m)*negpoly(n)),x)
                    lhs=sum(c*beta_int(b+j[0],N-b) for j,c in product.terms())
                    check('negative_sector_beta_closure',lhs-rhs)
    # Local Gamma-product coefficients and the all-logarithmic depth cancellation.
    reductions=[]
    for r in range(9):
        out=defaultdict(lambda:S.Integer(0))
        for m in range(1,r+2):
            for key,coeff in Dmoment(m).items():
                out[key]+=S.factorial(r)*coeff
        out={k:S.expand(v) for k,v in out.items() if S.expand(v)!=0}
        assert max(1+len(k[1]) for k in out)<=r+1
        counts['logarithmic_depth_drop']+=1
        reductions.append({'r':r,'terms':[{'outer_order':f's{key[0]:+d}', 'inner_indices':list(key[1]),
                                            'coefficient':str(coeff)} for key,coeff in sorted(out.items())]})
    # Local expansion is checked independently using finite strict/star products.
    # Use integer s so all coefficients are rational combinations of formal c_{2j}.
    def conv(a,b):
        return [S.expand(sum(a[j]*b[k-j] for j in range(k+1))) for k in range(7)]
    for kval in (2,4,7):
        R=[S.Integer(0)]*7
        for j in range(4): R[2*j]=S.Integer(1) if j==0 else S.Symbol(f'c{2*j}')
        P=[S.Integer(1)]+[S.Integer(0)]*6
        Q=[S.Integer(1)]+[S.Integer(0)]*6
        for j in range(1,kval):
            P=conv(P,[S.Integer(1),-1/S.Integer(j)]+[S.Integer(0)]*5)
            Q=conv(Q,[(-1/S.Integer(j))**k for k in range(7)])
        for sval in (3,5):
            A=[S.Integer(1)]+[S.Integer(0)]*6
            for _ in range(sval-1): A=conv(A,[1/S.Integer(kval)**j for j in range(7)])
            direct=conv(conv(R,A),P)
            for ell in range(1,7):
                pred=0
                for v in range(ell//2+1):
                    cv=S.Integer(1) if v==0 else S.Symbol(f'c{2*v}')
                    for j in range(ell-2*v+1):
                        d=ell-2*v-j
                        pred+=cv*S.rf(sval-1,j)/S.factorial(j)/S.Integer(kval)**j*P[d]
                pred-=Q[ell]
                check('gamma_collision_coefficients',direct[ell]-Q[ell]-pred)
    # Corruption controls: make sure an altered polynomial is actually rejected.
    correct=closure_poly(2,1,0)
    altered=correct+1
    assert sum(c*Eneg(d[0]) for d,c in S.Poly(altered,p).terms()) != S.Rational(1,3)
    counts['rejected_corruptions']+=1
    assert S.expand(Cneg(1,2)+1+Cneg(2,1)-Dneg(1)*Dneg(2)-Dneg(3)) != 0
    counts['rejected_corruptions']+=1
    (ROOT/'results').mkdir(exist_ok=True)
    payload={'status':'PASS','sympy_version':S.__version__,'assertions_by_family':dict(counts),
             'total_passed_assertions':sum(counts.values()),
             'scope':'Exact finite symbolic checks; analytic proofs are in article.tex.'}
    (ROOT/'results'/'exact_checks.json').write_text(json.dumps(payload,indent=2)+'\n')
    (ROOT/'results'/'moment_reductions.json').write_text(json.dumps({'convention':'zeta_k denotes the Riemann zeta value at k; outer index is s+offset; valid first for Re(s)>2.', 'reductions':reductions},indent=2)+'\n')
    print(json.dumps(payload,indent=2))

if __name__=='__main__':
    run()
