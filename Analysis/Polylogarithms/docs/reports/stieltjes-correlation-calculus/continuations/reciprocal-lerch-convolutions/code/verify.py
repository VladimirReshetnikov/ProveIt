#!/usr/bin/env python3
"""Independent finite checks and floating-point diagnostics for the article.

Run from any directory: python code/verify.py [--exact-only]
Outputs are written beneath data/. These are not interval certificates and
not proof-assistant verification. All analytic arguments are in article.tex.
"""
from __future__ import annotations
import argparse
import json
import math
import platform
import time
from pathlib import Path
import mpmath as mp
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
X,T,U,P,s,t,W = sp.symbols('X T U P s t W')
EXACT: list[dict] = []
NUMERIC: list[dict] = []
NEGATIVE: list[dict] = []

def check(name: str, expression, expected=0) -> None:
    delta=sp.cancel(sp.expand(expression-expected))
    if delta != 0:
        raise AssertionError(f'{name}: {delta}')
    EXACT.append({'name': name, 'status': 'pass'})

def cp(r: int):
    if r < 1: raise ValueError('depth must be positive')
    if r % 2:
        return sp.sympify(sp.prod(X**2+(2*j-1)**2*P for j in range(1,(r-1)//2+1)))
    return X*sp.prod(X**2+(2*j)**2*P for j in range(1,r//2))

def rp(n: int, z=s):
    out=sp.Integer(1)
    for _ in range(n):
        out=sp.expand((T+z*U)*out+(P+T*T)*sp.diff(out,T)+U*U*sp.diff(out,U))
    return out

def exact_checks() -> None:
    # Independent coefficient construction versus a two-step recursion.
    recurrence={1:sp.Integer(1),2:X}
    for r in range(1,13):
        if r>2: recurrence[r]=sp.expand((X*X+(r-2)**2*P)*recurrence[r-2])
        check(f'central recurrence depth {r}',cp(r),recurrence[r])
        check(f'central parity depth {r}',cp(r).subs(X,-X),(-1)**(r-1)*cp(r))
        # Derivative recurrence of cosecant powers in an abstract cotangent.
        D=lambda q: sp.expand(-(P+T*T)*sp.diff(q,T)-r*T*q)
        check(f'cosecant ODE depth {r}',D(-r*T),r*(r+1)*(P+T*T)-r*r*P)
    for k in range(1,17):
        numerator=sp.rf(s,k)-(-1)**k*sp.rf(t,k)
        q,rem=sp.div(sp.expand(numerator),s+t+k-1,t)
        check(f'pole cancellation Q{k}',rem)
        check(f'Q{k} reciprocity',q.xreplace({s:t,t:s}),(-1)**(k+1)*q)
    for n in range(0,9):
        # Check the differential polynomial against literal differentiation.
        z,h,g=sp.symbols('z h g')
        p=sp.symbols('p')
        # Abstract derivative, including g'=-T*g and h'=1.
        literal=g*h**(-s)
        for _ in range(n):
            literal=sp.expand(-(-T*g*sp.diff(literal,g)
                         -(P+T*T)*sp.diff(literal,T)+sp.diff(literal,h)))
        check(f'weighted transform polynomial {n}',
              sp.expand(literal/(g*h**(-s))).subs(h,1/U),rp(n))
    for j in range(1,17):
        z=sp.symbols('z')
        bell=[sp.Integer(1)]
        for n in range(1,j):
            bell.append(sp.expand(sum(sp.binomial(n-1,k-1)*(-1)**(k-1)*sp.factorial(k-1)*sp.harmonic(j-1,k)*bell[n-k] for k in range(1,n+1))))
        for h in range(1,j+1):
            actual=sp.expand(sp.rf(z,j)).coeff(z,h)*sp.factorial(h)
            check(f'harmonic derivative j{j} h{h}',actual,
                  h*sp.factorial(j-1)*bell[h-1])
    # Partial fractions: compute coefficients locally and compare globally.
    z=sp.symbols('z')
    configs=[([sp.Rational(2,3),sp.Rational(7,4)],[1,1]),
             ([sp.Rational(1,2),sp.Rational(3,2)],[2,3]),
             ([sp.Rational(2,5),sp.Rational(6,5),sp.Rational(13,5)],[2,1,2]),
             ([1,2,4],[3,2,1])]
    for ci,(aa,mm) in enumerate(configs):
        f=sp.prod((z+a-1)**(-m) for a,m in zip(aa,mm))
        partial=0
        u=sp.symbols('u')
        for nu,(a,m) in enumerate(zip(aa,mm)):
            local=sp.prod((u+b-a)**(-n) for ro,(b,n) in enumerate(zip(aa,mm)) if ro!=nu)
            for k in range(1,m+1):
                coeff=sp.diff(local,u,m-k).subs(u,0)/sp.factorial(m-k)
                partial+=coeff*(z+a-1)**(-k)
        check(f'unequal shifts partial fraction {ci}',f,partial)
    # A resonant product is not the product of its point values.
    check('depth four W=-2 residue term',sp.rf(W,2).subs(W,-2)/6,sp.Rational(1,3))
    for r in range(2,13):
        # First moments sum to mu*C; at mu=0 their sum vanishes.
        orders=sp.symbols('v:'+str(r))
        total=sum(orders)
        check(f'first moment conservation depth {r}',sum(v-total/r for v in orders))
    # Full all-depth moment reduction versus the independent r=2 Q-polynomial.
    def reduce_center(poly, total):
        out={}
        for (bt,du),co in sp.Poly(poly,T,U).terms():
            k=bt//2
            for q in range(k+1):
                c=co*sp.binomial(k,q)*(-P)**(k-q)
                rr=2+2*q
                vv=total+du
                if bt%2: c=-c*vv/rr; vv+=1
                # C_{rr}(vv;0) in the E(vv+2j) basis.
                pol=sp.Poly(cp(rr),X)
                for (power,),a in pol.terms():
                    shift=sp.expand(vv-total+power-1)
                    value=c*a*sp.rf(vv,power-1)/sp.factorial(rr-1)
                    out[shift]=out.get(shift,0)+value
        return {k:sp.expand(v) for k,v in out.items()}
    for ell in range(9):
        left=reduce_center(rp(ell,s),s+t)
        right={}
        for j in range(ell//2+1):
            k=ell-2*j+1
            d=sp.Integer(1) if j==0 else 2*(1-sp.Rational(2)**(1-2*j))*sp.zeta(2*j).expand(func=True)
            d=sp.expand(d).subs(sp.pi**(2*j),P**j) if j else d
            q=sp.cancel((sp.rf(s,k)-(-1)**k*sp.rf(t,k))/(s+t+k-1))
            right[ell-2*j]=sp.factorial(ell)*d*q/sp.factorial(k)
        for shift in set(left)|set(right):
            check(f'independent moment ell{ell} shift{shift}',left.get(shift,0),right.get(shift,0))
    # Complete harmonic / reciprocal-product coefficients, independently built.
    for n in range(1,11):
        hs=[sp.Integer(1)]
        for v in range(1,8):
            hs.append(sp.expand(sum(sp.harmonic(n,j)*hs[v-j] for j in range(1,v+1))/v))
        for q in range(1,9):
            lhs=sum((-1)**k*sp.binomial(n,k)*sp.harmonic(k,q) for k in range(n+1))/sp.factorial(n)
            check(f'consecutive harmonic n{n} q{q}',lhs,-hs[q-1]/(n*sp.factorial(n)))
    def lattice(nn):
        r=len(nn); out=0
        for nu,N in enumerate(nn):
            c=1/sp.prod(sp.Integer(M-N) for rho,M in enumerate(nn) if rho!=nu)
            for (j,),a in sp.Poly(cp(r),X).terms():
                h=sp.harmonic(N,j+1) if r%2==0 else sum(sp.Rational((-1)**(v-1),v**(j+1)) for v in range(1,N+1))
                out-=c*a*sp.factorial(j)*h*(1 if r%2==0 else (-1)**N)/sp.factorial(r-1)
        return sp.expand(out)
    check('triple lattice exact example',lattice([0,2,4]),sp.Rational(1475,13824)+5*P/192)
    check('quadruple lattice exact example',lattice([0,1,2,3]),sp.Rational(575,3888)+11*P/162)
    # Deliberate wrong normalizations must not pass.
    for name,bad,good in [('missing half in first moment',s-t,(s-t)/2),
                         ('dropped resonant third',0,sp.Rational(1,3)),
                         ('wrong p4 constant',X*(X*X+3*P),cp(4))]:
        if sp.expand(bad-good)==0: raise AssertionError('negative control failed')
        NEGATIVE.append({'name':name,'status':'rejected as expected'})
    (ROOT/'data'/'central_polynomials.json').write_text(json.dumps(
        {'variable':'X; P denotes pi^2','polynomials':{str(r):str(sp.expand(cp(r))) for r in range(1,13)}},indent=2)+'\n')
    (ROOT/'data'/'moment_polynomials.json').write_text(json.dumps(
        {'variables':'T=pi*cot(pi*p), U=1/(p+a-1), P=pi^2',
         'R':{str(n):str(rp(n)) for n in range(9)},
         'Q':{str(k):str(sp.cancel((sp.rf(s,k)-(-1)**k*sp.rf(t,k))/(s+t+k-1))) for k in range(1,13)}},indent=2)+'\n')

def E(v,a):
    return mp.mpf(1) if v==0 else v*mp.zeta(v+1,a)

def eta(v,a):
    if v==1: return (mp.digamma((a+1)/2)-mp.digamma(a/2))/2
    return (mp.zeta(v,a/2)-mp.zeta(v,(a+1)/2))/mp.power(2,v)

def finite(r,v,a):
    ans=mp.mpf(0)
    for (power,),coef in sp.Poly(cp(r),X).terms():
        c=mp.mpf(str(coef.subs(P,sp.pi**2).evalf(mp.mp.dps+5)))
        ans+=c*(mp.rf(v,power-1)*E(v+power-1,a) if r%2==0
                 else mp.rf(v,power)*eta(v+power,a))
    return ans/mp.factorial(r-1)

def barnes(r,v,a,mu=0):
    c=mp.mpf('0.5') if mp.re(a)>mp.mpf('0.5') else 1-mp.re(a)/2
    f=lambda y: mp.exp((c+1j*y)*mu)*(mp.pi/mp.sin(mp.pi*(c+1j*y)))**r*(c+a-1+1j*y)**(-v)/(2*mp.pi)
    return mp.quad(f,[-mp.inf,-2,-mp.mpf('0.5'),0,mp.mpf('0.5'),2,mp.inf])

def diag(name,actual,expected,tol=mp.mpf('1e-40')):
    err=abs(actual-expected)/max(1,abs(expected))
    if not err<tol: raise AssertionError(f'{name}: {mp.nstr(err,8)} actual={actual} expected={expected}')
    NUMERIC.append({'name':name,'relative_scaled_error':mp.nstr(err,8),'tolerance':str(tol),'status':'pass'})
    print(name,mp.nstr(err,5),flush=True)

def numeric_checks():
    mp.mp.dps=55
    # Independent contour integral; includes fractional, negative, complex orders,
    # and a shift below 1/2, where the symmetric line is not admissible.
    for r in range(1,9):
        for v in [mp.mpf('0'),mp.mpf('-2'),mp.mpf('0.7')+mp.mpf('0.35')*1j]:
            a=mp.mpf('1.2')+mp.mpf('0.15')*1j
            diag(f'Barnes finite r{r} W{v}',barnes(r,v,a),finite(r,v,a))
    for a in [mp.mpf('0.25'),mp.mpf('0.5'),mp.mpf('2.0')]:
        diag(f'small/shifted a {a}',barnes(4,mp.mpf('-1.3'),a),finite(4,mp.mpf('-1.3'),a))
    # Direct one-dimensional convolution of elementary logistic kernels.
    def base(r,mu):
        pol=cp(r)
        if mu==0 and r%2==0:
            co=sp.Poly(pol,X).coeff_monomial(X).subs(P,sp.pi**2)
            return mp.mpf(str(co.evalf(65)))/mp.factorial(r-1)
        coeffs=sp.Poly(pol,X)
        val=sum(mp.mpf(str(co.subs(P,sp.pi**2).evalf(65)))*mu**j[0] for j,co in coeffs.terms())
        return val/(mp.factorial(r-1)*(1-(-1)**r*mp.exp(-mu)))
    logistic=lambda x:1/(1+mp.exp(-x))
    for r in range(2,9):
        for mu in [mp.mpf('-0.7'),mp.mpf('0'),mp.mpf('0.9')]:
            fun=lambda x:logistic(x)*base(r-1,mu-x)+logistic(-x)*base(r-1,mu+x)
            diag(f'elementary base convolution r{r} mu{mu}',mp.quad(fun,[0,1,4,12,mp.inf]),base(r,mu))
    # Direct reciprocal polylogarithm quadratures, split into a positive half-line.
    def fd(v,x):
        if v==0: return 1/(1+mp.exp(-x))
        if v==1: return mp.log1p(mp.exp(x))
        return -mp.polylog(v,-mp.exp(x))
    def moment(ell,sv,tv):
        fun=lambda x: x**ell*(fd(sv,x)*fd(tv,-x)+(-1)**ell*fd(sv,-x)*fd(tv,x))
        return mp.quad(fun,[0,1,4,12,mp.inf])
    def moment_formula(ell,sv,tv):
        total=sv+tv; val=0
        for j in range(ell//2+1):
            k=ell-2*j+1
            poly=sp.cancel((sp.rf(s,k)-(-1)**k*sp.rf(t,k))/(s+t+k-1))
            q=mp.mpc(str(sp.re(poly.subs({s:sv,t:tv})).evalf(65)),str(sp.im(poly.subs({s:sv,t:tv})).evalf(65)))
            d=1 if j==0 else 2*(1-2**(1-2*j))*mp.zeta(2*j)
            val+=mp.factorial(ell)*d*q*E(total+ell-2*j,1)/mp.factorial(k)
        return val
    for sv,tv in [(0,0),(1,0),(1,1),(2,1),(2,2),(-1,2)]:
        for ell in [0,1,2]:
            diag(f'direct Li moment ({sv},{tv}) ell{ell}',moment(ell,sv,tv),moment_formula(ell,sv,tv))
    # Direct noninteger order, with no integer-order inversion used.
    diag('direct noninteger reciprocal Li',moment(0,mp.mpf('0.6'),mp.mpf('1.3')),E(mp.mpf('1.9'),1),mp.mpf('1e-37'))
    # Nonzero fugacity checks use the analytic finite Lerch/polylog combination.
    for mu in [mp.mpf('-0.8'),mp.mpf('0.6')]:
        for r in [2,3,4]:
            v=mp.mpf('1.25'); val=0; pol=cp(r)
            for j in range(r):
                coeff=mp.mpf(str(sp.diff(pol,X,j).subs({X:sp.Float(str(mu),mp.mp.dps+10),P:sp.pi**2}).evalf(65)))
                z=(-1)**r*mp.exp(mu)
                # a=1: Phi(z,q,1)=Li_q(z)/z.
                val+=(-1)**j*coeff*mp.rf(v,j)*mp.polylog(v+j,z)/mp.factorial(j)
            val=-val/mp.factorial(r-1)
            diag(f'fugacity r{r} mu{mu}',barnes(r,v,1,mu),val,mp.mpf('1e-38'))
    # Independent Stieltjes and Gamma diagnostics use elementary log moments on
    # the vertical line, not finite-differenced pole-containing zeta formulas.
    for a in [mp.mpf('0.8'),mp.mpf('1.4')]:
        b=a-mp.mpf('0.5')
        for m in range(1,5):
            f=lambda y:(mp.pi/mp.cosh(mp.pi*y))**2*(-mp.log(b+1j*y))**m/(2*mp.pi)
            actual=mp.quad(f,[-mp.inf,-1,0,1,mp.inf])
            diag(f'Stieltjes Gamma-weighted a{a} M{m}',actual,(-1)**(m-1)*m*mp.stieltjes(m-1,a))
        fun=lambda y:(mp.pi/mp.cosh(mp.pi*y))**2*((b+1j*y)*mp.log(b+1j*y)-(b+1j*y))/(2*mp.pi)
        diag(f'log Gamma weighted a{a}',mp.quad(fun,[-mp.inf,-1,0,1,mp.inf]),mp.loggamma(a)-mp.log(2*mp.pi)/2)
    # Higher-depth spectral jets and unequal integral-shift examples.
    for a in [mp.mpf('0.8'),mp.mpf('1.4')]:
        b=a-mp.mpf('0.5')
        for m in [1,2]:
            fun=lambda y:(mp.pi/mp.cosh(mp.pi*y))**4*(-mp.log(b+1j*y))**m/(2*mp.pi)
            expected=(2*mp.pi**2*mp.stieltjes(0,a)/3+mp.zeta(3,a)/3) if m==1 else (-4*mp.pi**2*mp.stieltjes(1,a)/3+mp.zeta(3,a)+2*mp.diff(lambda v:mp.zeta(v,a),3)/3)
            diag(f'depth four jet a{a} M{m}',mp.quad(fun,[-mp.inf,-1,0,1,mp.inf]),expected)
    for aa,expected in [([1,3,5],mp.mpf(1475)/13824+5*mp.pi**2/192),
                        ([1,2,3,4],mp.mpf(575)/3888+11*mp.pi**2/162)]:
        fun=lambda y:(mp.pi/mp.cosh(mp.pi*y))**len(aa)*mp.fprod(1/(a-mp.mpf('0.5')+1j*y) for a in aa)/(2*mp.pi)
        diag(f'unequal lattice {aa}',mp.quad(fun,[-mp.inf,-1,0,1,mp.inf]),expected)
    # Direct Gaussian arctangent instance and a harmonic remainder.
    diag('Gaussian arctangent',mp.quad(lambda x:2*mp.atan(mp.exp(x))*mp.atan(mp.exp(-x)),[0,1,5,mp.inf]),7*mp.zeta(3)/4)
    rem=lambda x:(mp.log1p(mp.exp(x))-mp.exp(x))*(mp.log1p(mp.exp(-x))-mp.exp(-x))
    # Bounded truncation is a diagnostic, not an interval-certified tail.
    diag('harmonic remainder N1',mp.quad(lambda x:2*rem(x),[0,1,5,20,100]),2*(mp.zeta(3)-1),mp.mpf('1e-37'))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--exact-only',action='store_true')
    args=parser.parse_args(); start=time.time()
    (ROOT/'data').mkdir(exist_ok=True)
    exact_checks()
    if not args.exact_only: numeric_checks()
    result={'evidence':'finite exact identities and non-rigorous floating-point diagnostics; not a proof assistant or interval certificate',
            'python':platform.python_version(),'sympy':sp.__version__,'mpmath':mp.__version__,
            'working_decimal_digits':55 if not args.exact_only else None,
            'exact_count':len(EXACT),'numerical_count':len(NUMERIC),'negative_control_count':len(NEGATIVE),
            'exact':EXACT,'numerical':NUMERIC,'negative_controls':NEGATIVE,
            'elapsed_seconds':round(time.time()-start,3)}
    target=ROOT/'data'/('verification_exact.json' if args.exact_only else 'verification.json')
    target.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('exact','numerical','negative_controls')},indent=2))
if __name__=='__main__': main()
