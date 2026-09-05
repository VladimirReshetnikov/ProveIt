#!/usr/bin/env python3
"""Reproduce exact coefficients and numerical tests for the accompanying article.
Requires Python 3.10+, SymPy and mpmath. No network or external data are used.
Numerical checks are high-precision tests, not interval-arithmetic certificates.
"""
from __future__ import annotations
import itertools
import json
from functools import lru_cache
from math import factorial, comb
from pathlib import Path
import sympy as s
import mpmath as mp


def weighted_partitions(n: int, j: int = 1):
    """Yield multiplicity dictionaries with sum(j*k[j]) == n."""
    if n == 0:
        yield {}
    elif j <= n:
        for k in range(n // j + 1):
            for tail in weighted_partitions(n - j*k, j + 1):
                yield ({j: k, **tail} if k else tail)


def exp_coeff(ds: list, n: int):
    if n == 0:
        return s.Integer(1)
    return s.factor(sum(s.prod(ds[j-1]**k / s.factorial(k) for j,k in p.items())
                        for p in weighted_partitions(n)))


def log_coeff(us: list, n: int):
    ans = 0
    for p in weighted_partitions(n):
        r = sum(p.values())
        ans += (-1)**(r+1)*s.factorial(r-1)*s.prod(us[j-1]**k/s.factorial(k) for j,k in p.items())
    return s.factor(ans)


@lru_cache(None)
def gamma_ratio_coeff(a, b, n):
    ds = [(-1)**(m+1)*(s.bernoulli(m+1,a)-s.bernoulli(m+1,b))/(m*(m+1))
          for m in range(1,n+1)]
    return exp_coeff(ds,n)


def endpoint_coeff(alpha, c, n):
    p = alpha+1
    return s.factor(sum(s.binomial(alpha,j)*(-c)**j*s.rf(p,j)*
                        gamma_ratio_coeff(s.Integer(1),j+p+1,n-j) for j in range(n+1)))


def normal_moment(n: int, mu=s.Rational(1,2)):
    return sum(s.factorial(n)*mu**(n-2*j)/(4**j*s.factorial(j)*s.factorial(n-2*j))
               for j in range(n//2+1))


def involution_coeff(n: int):
    ans = 0
    for p in weighted_partitions(n):
        power = sum((r+2)*k for r,k in p.items())
        fac = s.prod(s.Rational((-1)**(r+1),r+2)**k/s.factorial(k) for r,k in p.items())
        ans += fac*normal_moment(power)
    return s.factor(ans)


def linear_log_inverse_coeff(ds: list, a, b, nmax: int):
    # Triangular coefficient extraction, independently checking the closed formula.
    t = s.Symbol('t')
    out=[]
    U=s.Integer(0)
    for n in range(1,nmax+1):
        R=b*s.log(1+t*U)+sum(ds[j-1]*(t/(1+t*U))**j for j in range(1,n+1))
        cn=s.factor(-s.expand(s.series(R,t,0,n+1).removeO()).coeff(t,n)/a)
        out.append(cn); U+=cn*t**n
    return out


def iv_inverse_coeff(hs, nmax):
    e, lam = s.symbols('e lam', positive=True)
    V=-2/lam
    out=[V]
    for n in range(1,nmax+1):
        u=e*V
        # Expand elementary pieces only to required order.
        nonlinear=sum((-1)**k*u**k/(k*(k-1)) for k in range(2,n+2))/e
        root=2*sum(s.binomial(s.Rational(1,2),k)*u**k for k in range(n+1))
        tail=2*e*sum(hs[j-1]*e**j*(1+u)**(-s.Rational(j,2)) for j in range(1,n))
        residual=nonlinear+root+tail
        dn=s.factor(-s.series(residual,e,0,n+1).removeO().expand().coeff(e,n)/lam)
        out.append(dn); V+=dn*e**n
    return out


def mfloat(x):
    return mp.mpf(str(s.N(x,mp.mp.dps+10)))


def endpoint_block(x, alpha, negative=False):
    alpha=mp.mpf(alpha); p=alpha+1
    C=1/(2*mp.pi) if alpha==mp.mpf('0.5') else 1/mp.pi
    c=mp.mpf(1)/4 if negative else mp.mpf(3)/4
    pref=C*4**alpha*(1 if negative else 3**(x+p))
    return pref*mp.beta(p,x+1)*mp.hyp2f1(-alpha,p,x+p+1,c)


def iv_block_log(x, sig=1):
    """Stable quadrature after centering at the exact positive saddle."""
    r=(sig+mp.sqrt(1+4*x))/2
    ph=x*mp.log(r)-(r-sig)**2/2
    f=lambda v: mp.exp(x*mp.log1p(v/r)-r*v+sig*v-v*v/2) if v > -r else mp.mpf('0')
    J=mp.quad(f,[-r,-min(r/2,mp.mpf(8)),0,8,mp.inf])
    return ph+mp.log(J)-mp.log(2*mp.pi)/2


def exact_iv(n: int):
    return sum(factorial(n)//(2**j*factorial(j)*factorial(n-2*j)) for j in range(n//2+1))


def stirling_interp(x, k: int):
    return sum((-1)**(k-j)*comb(k,j)*mp.power(j,x) for j in range(1,k+1))/factorial(k)


def finite_exp_inverse(k: int, y, max_degree: int):
    a=mp.log(k); X=mp.log(factorial(k)*y)/a
    kappas=[mp.log(mp.mpf(k)/j)/a for j in range(1,k)]
    qs=[(-1)**(k-j)*comb(k,j)*mp.power(mp.mpf(j)/k,X) for j in range(1,k)]
    value=X
    for nu in itertools.product(range(max_degree+1),repeat=k-1):
        r=sum(nu)
        if 1<=r<=max_degree:
            K=sum(n*v for n,v in zip(nu,kappas))
            fall=mp.fprod(K-h for h in range(1,r))
            term=-fall*mp.fprod(q**n/factorial(n) for q,n in zip(qs,nu))/a
            value+=term
    return value


def q_log_h(r: int, q):
    return -2/(r*(q**r-1))+(2/(r*(q**(r//2)-1)) if r%2==0 else 0)


def main():
    mp.mp.dps=90
    result={}
    inv=[involution_coeff(n) for n in range(9)]
    assert inv[:4]==[1,s.Rational(7,24),-s.Rational(119,1152),-s.Rational(7933,414720)]
    result['involution_coefficients']=[str(v) for v in inv]
    hs=[log_coeff(inv[1:],n) for n in range(1,7)]
    result['involution_log_coefficients']=[str(v) for v in hs]
    ivc=iv_inverse_coeff(hs,3)
    result['involution_inverse_V_coefficients']=[str(v) for v in ivc]
    endpoint={}
    for alpha,name in [(s.Rational(1,2),'Motzkin'),(-s.Rational(1,2),'trinomial')]:
        endpoint[name]={}
        for c,which in [(s.Rational(3,4),'plus'),(s.Rational(1,4),'minus')]:
            endpoint[name][which]=[str(endpoint_coeff(alpha,c,n)) for n in range(7)]
    result['endpoint_coefficients']=endpoint
    ds=[s.Rational((-1)**(m+1),m*(m+1))*(s.bernoulli(m+1,1)/2**m-s.bernoulli(m+1,1)-s.bernoulli(m+1,2)) for m in range(1,7)]
    cs=[exp_coeff(ds,n) for n in range(7)]
    assert cs[:4]==[1,-s.Rational(9,8),s.Rational(145,128),-s.Rational(1155,1024)]
    result['catalan_log_coefficients']=[str(v) for v in ds]
    result['catalan_coefficients']=[str(v) for v in cs]
    a=s.Symbol('a',positive=True)
    civ=linear_log_inverse_coeff(ds,a,-s.Rational(3,2),4)
    result['catalan_inverse_coefficients']=[str(v) for v in civ]
    # Exact identity checks for endpoint integral interpolations.
    for n in range(21):
        M=sum(comb(n,2*j)*comb(2*j,j)//(j+1) for j in range(n//2+1))
        T=sum(comb(n,2*j)*comb(2*j,j) for j in range(n//2+1))
        for al,ex in [(mp.mpf('.5'),M),(mp.mpf('-.5'),T)]:
            got=endpoint_block(n,al)+(-1)**n*endpoint_block(n,al,True)
            assert abs(got-ex)<mp.mpf('1e-70')*max(1,ex)
    # Exact finite polynomial identity for Gaussian central binomials q=2.
    for n in range(1,13):
        exact=mp.fprod((mp.mpf(2)**(2*n-j)-1)/(mp.mpf(2)**(n-j)-1) for j in range(n))
        Q=mp.mpf('.5'); t=Q**n; P=mp.qp(Q,Q)
        got=mp.power(2,n*n)/P*mp.qp(Q*t,Q)**2/mp.qp(Q*t*t,Q)
        assert abs(got/exact-1)<mp.mpf('1e-75')
    result['identity_tests']='PASS: 42 endpoint values n=0..20 and 12 Gaussian binomial values n=1..12'
    # Forward relative errors, all computed independently from exact sequence formulas.
    fw=[]
    n=100
    exact=mp.mpf(comb(2*n,n))/(n+1)
    approx=mp.power(4,n)/(mp.sqrt(mp.pi)*mp.power(n,mp.mpf('1.5')))*sum(mfloat(cs[j])/n**j for j in range(6))
    fw.append(['Catalan',n,5,mp.nstr(abs(approx/exact-1),10)])
    exact=mp.mpf(exact_iv(n))
    leading=mp.exp(n*mp.log(n)/2-n/2+mp.sqrt(n)-mp.mpf(1)/4)/mp.sqrt(2)
    approx=leading*(sum(mfloat(inv[j])/mp.power(n,mp.mpf(j)/2) for j in range(7))+mp.exp(-2*mp.sqrt(n))*sum((-1)**j*mfloat(inv[j])/mp.power(n,mp.mpf(j)/2) for j in range(7)))
    fw.append(['Involutions (both blocks)',n,6,mp.nstr(abs(approx/exact-1),10)])
    for al,name in [(s.Rational(1,2),'Motzkin'),(-s.Rational(1,2),'Central trinomial')]:
        p=mfloat(al+1); C=1/(2*mp.pi) if al>0 else 1/mp.pi
        cp=C*mp.power(3,p)*mp.power(4,mfloat(al))*mp.gamma(p)
        cm=C*mp.power(4,mfloat(al))*mp.gamma(p)
        ap=sum(mfloat(endpoint_coeff(al,s.Rational(3,4),j))/n**j for j in range(6))
        am=sum(mfloat(endpoint_coeff(al,s.Rational(1,4),j))/n**j for j in range(6))
        approx=(cp*mp.power(3,n)*ap+(-1)**n*cm*am)/mp.power(n,p)
        exact=endpoint_block(n,mfloat(al))+(-1)**n*endpoint_block(n,mfloat(al),True)
        fw.append([name,n,5,mp.nstr(abs(approx/exact-1),10)])
    result['forward_relative_errors']=fw
    # Inverse tests: target y=F(n) means true index is exactly n.
    rows=[]
    n=100
    L=mp.log(mp.mpf(comb(2*n,n))/(n+1)*mp.sqrt(mp.pi)); aa=mp.log(4); b=-mp.mpf('1.5')
    X=b/aa*mp.lambertw(aa/b*mp.exp(L/b),-1)
    for N in [0,1,2,4]:
        value=X+sum(mfloat(civ[j-1].subs(a,s.log(4)))/X**j for j in range(1,N+1))
        rows.append(['Catalan',n,str(N),mp.nstr(abs(value-n),10)])
    n=30; y=stirling_interp(n,3)
    for N in [0,1,2,3,4]:
        value=finite_exp_inverse(3,y,N)
        rows.append(['Stirling k=3',n,str(N),mp.nstr(abs(value-n),10)])
    n=100; y=mp.mpf(exact_iv(n)); L=2*mp.log(y)+mp.mpf('.5')+mp.log(2)
    X=L/mp.lambertw(L/mp.e); lam=mp.log(X)
    for N in [-1,0,1,2,3]:
        val=X if N==-1 else X+mp.sqrt(X)*sum(mfloat(ivc[j].subs(s.Symbol('lam',positive=True),lam))/mp.power(X,mp.mpf(j)/2) for j in range(N+1))
        rows.append(['Involutions',n,'core' if N==-1 else 'V0..V'+str(N),mp.nstr(abs(val-n),10)])
    n=20; q=mp.mpf(2); aa=mp.log(q); Q=1/q; P=mp.qp(Q,Q)
    y=mp.fprod((q**(2*n-j)-1)/(q**(n-j)-1) for j in range(n))
    X=mp.sqrt(mp.log(y*P)/aa); T=mp.exp(-aa*X)
    d1=1/(aa*(q-1)*X)
    d2=-q/(2*aa*(q*q-1)*X)-1/(aa*(q-1)**2*X**2)-1/(2*aa**2*(q-1)**2*X**3)
    for N,value in [(0,X),(1,X+d1*T),(2,X+d1*T+d2*T*T)]:
        rows.append(['Gaussian binomial q=2',n,str(N),mp.nstr(abs(value-n),10)])
    result['inverse_absolute_errors']=rows
    # Isolate the exponentially small saddle sector using exact positive block.
    n=100
    lp=iv_block_log(mp.mpf(n),1); lm=iv_block_log(mp.mpf(n),-1)
    result['involution_negative_positive_ratio_at_100']=mp.nstr(mp.exp(lm-lp),25)
    assert abs((mp.exp(lp)+mp.exp(lm))/exact_iv(n)-1)<mp.mpf('1e-70')
    # A positive-block inverse displaced from n by the exact exponentially small sector.
    phip=mp.diff(lambda x: iv_block_log(x,1),mp.mpf(n))
    first=mp.exp(lm-lp)/phip
    result['involution_expected_positive_core_displacement_at_100']=mp.nstr(first,25)
    result['numerical_precision_decimal_digits']=mp.mp.dps
    path=Path(__file__).with_name('verification_results.json')
    path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    main()
