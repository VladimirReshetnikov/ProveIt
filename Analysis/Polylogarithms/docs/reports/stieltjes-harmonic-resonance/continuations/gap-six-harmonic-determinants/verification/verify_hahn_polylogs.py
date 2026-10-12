#!/usr/bin/env python3
"""Independent exact and high-precision checks for the harmonic/Hahn section.

Run from any directory. Requires sympy and mpmath. Decimal quadratures are
diagnostics, not interval proofs. The article supplies the analytic proofs.
"""
from __future__ import annotations
import itertools
import json
from pathlib import Path
import sympy as sp
import mpmath as mp

OUT = Path(__file__).resolve().parents[1] / "results" / "hahn_polylogs.json"
checks = 0

def check(condition):
    global checks
    assert condition
    checks += 1

def falling(x, k):
    return sp.prod(x-j for j in range(k))

def gram_polynomial(k, x, N):
    return sp.expand(sum((-1)**(k+j)*sp.binomial(k,j)*sp.binomial(k+j,j)
                         *falling(N-j,k-j)*falling(x,j)
                         for j in range(k+1))/sp.binomial(2*k,k))

def uniform_norm(k, N):
    return (sp.factorial(N+k+1)/(sp.Integer(2*k+1)*sp.factorial(N-k)
                                 *sp.binomial(2*k,k)**2))

def moments(r, N, a, eta):
    return sp.Matrix(r,r,lambda i,j:sum(sp.Integer(n)**(i+j)
        *(1/(n+a)+eta/(n+a+1)) for n in range(N+1)))

def harmonic_pencil(r, a, eta):
    u=sp.Matrix([(-a)**i for i in range(r)])
    v=sp.Matrix([(-a-1)**i for i in range(r)])
    return u*u.T+eta*v*v.T

def top_coefficient(r,N,a,eta):
    mat=moments(r,N,a,eta)
    hh=sum(1/(n+a) for n in range(N+1))
    C=harmonic_pencil(r,a,eta)
    D=mat-hh*C
    values=[sp.cancel((D+j*C).det()) for j in range(5)]
    check(sp.cancel(values[3]-3*values[2]+3*values[1]-values[0])==0)
    check(sp.cancel(values[4]-3*values[3]+3*values[2]-values[1])==0)
    return sp.cancel((values[2]-2*values[1]+values[0])/2)

def hahn_top(r,N,a,eta):
    q=r-2
    t=1+eta
    roots=[-a,-a-1,-a-1/t]
    H=sp.prod(uniform_norm(j,N) for j in range(q))
    mat=sp.Matrix([[gram_polynomial(q+j,c,N) for j in range(3)] for c in roots])
    return sp.cancel((-1)**q*t**r*H*mat.det())

def direct_ensemble(r,N):
    value=sp.S.Zero
    for nodes in itertools.combinations(range(N+1),r):
        delta=sp.prod((nodes[j]-nodes[i])**2 for i in range(r) for j in range(i+1,r))
        value+=sp.Rational(delta,sp.prod((n+1)*(n+2) for n in nodes))
    return sp.cancel(value)

def triple_formula(M):
    M=sp.Integer(M)
    H=sp.harmonic(M)
    return sp.cancel(-M*(M+1)*(M+2)*H**2/3
                     +4*M**2*(M+2)*H/3
                     +M**3*(M**2-18*M-31)/(12*(M+1)))

def exact_checks():
    x=sp.symbols('x')
    for N in [4,6,9]:
        polys=[gram_polynomial(k,x,N) for k in range(5)]
        for k,p in enumerate(polys):
            check(sp.Poly(p,x).LC()==1)
            check(sum(p.subs(x,n)**2 for n in range(N+1))==uniform_norm(k,N))
            for j in range(k):
                check(sum(p.subs(x,n)*polys[j].subs(x,n) for n in range(N+1))==0)
    for r in range(2,7):
        N=r+2
        for a,eta in [(sp.Rational(1,2),sp.Integer(2)),
                      (sp.Integer(1),sp.I),
                      (sp.Rational(3,2),(sp.I-2)/3)]:
            actual=top_coefficient(r,N,a,eta)
            check(sp.cancel(actual-hahn_top(r,N,a,eta))==0)
            q=r-2
            G=sp.Matrix(q,q,lambda i,j:sum((n+a)*(n+a+1)
                *((1+eta)*(n+a)+1)*sp.Integer(n)**(i+j) for n in range(N+1)))
            check(sp.cancel(actual-eta*G.det())==0)
    for M in range(1,13):
        check(triple_formula(M)==direct_ensemble(3,M-1))
    for r in range(2,7):
        eta,X,t=sp.symbols('eta X t')
        e0=sp.eye(r)[:,0];e1=sp.eye(r)[:,1]
        v=sp.Matrix([(-1)**i for i in range(r)])
        C=e0*e0.T+eta*v*v.T
        A=X*C-eta*e0*e0.T-e0*e1.T-e1*e0.T
        residue=sp.expand((A+eta*t*v*v.T).det()).coeff(t,1)
        expected=eta*(X-eta-2) if r==2 else -eta if r==3 else 0
        check(sp.expand(residue-expected)==0)
    x=sp.symbols('x')
    L=-sp.log(1-x)
    B=sp.polylog(2,x)+L**2
    # Expanding each input series first avoids asking SymPy to simplify
    # an identity in transcendental functions.
    Ls=sum(x**k/sp.Integer(k) for k in range(1,18))
    Bs=sum(x**k/sp.Integer(k)**2 for k in range(1,18))+Ls**2
    G=(-2*x*Bs/(1-x)**4
       +(3-14*x+15*x**2-2*x**3)*Ls/(3*x*(1-x)**4)
       +(18*x**3-31*x**2+31*x-6)/(6*(1-x)**5))
    series=sp.series(G,x,0,14).removeO().expand()
    for M in range(1,13):
        check(series.coeff(x,M)==triple_formula(M))

def numerical_checks():
    mp.mp.dps=75
    def z3(M):
        H=mp.harmonic(M)
        return (-M*(M+1)*(M+2)*H**2/3
                +mp.mpf(4)*M*M*(M+2)*H/3
                +mp.mpf(M)**3*(M*M-18*M-31)/(12*(M+1)))
    coefficients=[mp.mpf(str(triple_formula(M).p))/int(triple_formula(M).q)
                  for M in range(1,36)]
    def generator(x):
        if abs(x)<mp.mpf('0.0001'):
            return sum(coefficients[M-1]*x**M for M in range(1,36))
        L=-mp.log1p(-x);B=mp.polylog(2,x)+L*L
        return (-2*x*B/(1-x)**4
                +(3-14*x+15*x*x-2*x**3)*L/(3*x*(1-x)**4)
                +(18*x**3-31*x*x+31*x-6)/(6*(1-x)**5))
    diagnostics=[]
    for x in [mp.mpf('0.2'),mp.mpf('0.55'),mp.mpf('0.8')]:
        direct=sum(z3(M)*x**M for M in range(1,1001))
        error=abs(direct-generator(x))
        assert error<mp.mpf('1e-60')
        diagnostics.append({'test':'triple generator','x':str(x),'absolute_error':mp.nstr(error,8)})
    zz=lambda k:mp.zeta(k)
    expected=(-1+mp.mpf(13)*zz(2)/12-mp.mpf(31)*zz(3)/12
              +mp.mpf(5)*zz(4)/3+mp.mpf(41)*zz(5)/6
              -mp.mpf(97)*zz(6)/24-4*zz(7)
              -mp.mpf(7)*zz(2)*zz(3)/3+2*zz(3)**2
              +mp.mpf(2)*zz(2)*zz(5)/3+mp.mpf(5)*zz(3)*zz(4)/3)
    def integrand(x):
        if x==0:return mp.mpf(0)
        if x==1:return mp.mpf(1)/60
        return (-mp.log(x))**5*generator(x)/(120*x)
    value=mp.quad(integrand,[0,mp.mpf('.05'),mp.mpf('.4'),mp.mpf('.85'),1])
    error=abs(value-expected)
    assert error<mp.mpf('1e-55')
    diagnostics.append({'test':'sixth Euler endpoint','value':mp.nstr(value,65),
                        'closed_form':mp.nstr(expected,65),'absolute_error':mp.nstr(error,8)})
    return diagnostics

if __name__=='__main__':
    exact_checks()
    diagnostics=numerical_checks()
    OUT.parent.mkdir(parents=True,exist_ok=True)
    result={'exact_assertions':checks,'working_decimal_digits':75,
            'numerical_diagnostics':diagnostics,
            'scope':'Exact checks are finite algebraic verifications; quadratures are not interval certificates.'}
    OUT.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
