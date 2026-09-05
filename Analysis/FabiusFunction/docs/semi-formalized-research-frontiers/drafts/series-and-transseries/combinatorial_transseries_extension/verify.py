#!/usr/bin/env python3
"""Reproducible checks for Combinatorial Transseries and Their Inverses.

Run: python verify.py
Requires Python 3.10+, sympy and mpmath. No network or proprietary software.
Exact checks use rational arithmetic; numerical checks use 100-digit arithmetic.
The finite-order experiments are checks, not substitutes for the article's proofs.
"""
from __future__ import annotations
from math import comb, factorial
from pathlib import Path
import json
import sympy as sp
import mpmath as mp

mp.mp.dps = 100
t = sp.Symbol('t')


def trunc(expr, n: int):
    return sp.series(expr, t, 0, n + 1).removeO().expand()


def exp_coefficients(q: list, n: int) -> list:
    """Coefficient extraction from exp(sum q[j-1]*t**j), exactly."""
    out = [sp.S.One]
    for k in range(1, n + 1):
        out.append(sp.factor(sum(j*q[j-1]*out[k-j] for j in range(1,k+1))/k))
    return out


def log_coefficients(a: list, n: int) -> list:
    """a[0]=1. Return log coefficients at powers 1,...,n."""
    q = []
    for k in range(1, n+1):
        q.append(sp.factor(a[k]-sum(j*q[j-1]*a[k-j] for j in range(1,k))/sp.Integer(k)))
    return q


def gamma_ratio(a, b, n: int) -> list:
    """Gamma(x+a)/Gamma(x+b) = x**(a-b) * sum out[j]/x**j."""
    a,b=sp.sympify(a),sp.sympify(b)
    q=[(-1)**(j+1)*(sp.bernoulli(j+1,a)-sp.bernoulli(j+1,b))/sp.Integer(j*(j+1))
       for j in range(1,n+1)]
    return exp_coefficients(q,n)


def endpoint_coefficients(kind: str, n: int) -> list:
    if kind == 'motzkin_plus':
        nu, power, kappa, shift = sp.Rational(3,2), sp.Rational(1,2), sp.Rational(3,4), 1
    elif kind == 'motzkin_minus':
        nu, power, kappa, shift = sp.Rational(3,2), sp.Rational(1,2), sp.Rational(1,4), 1
    elif kind == 'delannoy':
        nu, power, kappa, shift = sp.Rational(1,2), -sp.Rational(1,2), (3+2*sp.sqrt(2))/(4*sp.sqrt(2)), 1
    elif kind == 'schroder':
        nu, power, kappa, shift = sp.Rational(3,2), sp.Rational(1,2), (3+2*sp.sqrt(2))/(4*sp.sqrt(2)), 0
    else:
        raise ValueError(kind)
    out=[]
    for m in range(n+1):
        out.append(sp.simplify(sum(sp.binomial(power,j)*(-kappa)**j*sp.rf(nu,j)*
                                  gamma_ratio(shift,shift+nu+j,m-j)[m-j]
                                  for j in range(m+1))))
    return out


def weight_vectors(n: int, first: int=1):
    """All finite multisets with sum(j*m_j)=n; dictionary keys are weights."""
    if n==0:
        yield {}
        return
    def rec(j, left, data):
        if j>n:
            if left==0:
                yield dict(data)
            return
        for count in range(left//j+1):
            if count:data[j]=count
            else:data.pop(j,None)
            yield from rec(j+1,left-j*count,data)
        data.pop(j,None)
    yield from rec(first,n,{})


def involution_coefficients(n: int) -> list:
    # R(t)=(t+sqrt(4+t^2))/2, b(t)=2-t/R(t), for the positive saddle.
    R=(t+sp.sqrt(4+t*t))/2
    b=2-t/R
    saddle=sp.S.One
    for w in range(1,n+1):
        for vect in weight_vectors(w):
            # A weight j corresponds to a phase derivative of order k=j+2.
            K=sum((j+2)*m for j,m in vect.items())
            M=sum(vect.values())
            if K%2: continue
            denom=sp.prod(sp.factorial(m)*sp.Integer(j+2)**m for j,m in vect.items())
            coef=(-1)**M*sp.factorial2(K-1)/denom
            saddle += coef*t**w*trunc(R**(-K)*b**(-sp.Rational(K,2)),n-w)
    # log R=asinh(t/2); writing it this way avoids symbolic log branch issues.
    rem=trunc(sp.asinh(t/2)/t**2+R/(2*t)-1/t-sp.Rational(1,4),n)
    pref=trunc(sp.exp(rem)*sp.sqrt(2/b),n)
    out=trunc(pref*saddle,n)
    return [sp.factor(out.coeff(t,j)) for j in range(n+1)]


def connected_graphs(n: int) -> list[int]:
    # Exact recurrence, independent of the asymptotic coefficient formula.
    out=[0]*(n+1)
    for k in range(1,n+1):
        out[k]=2**(k*(k-1)//2)-sum(comb(k-1,j-1)*out[j]*2**((k-j)*(k-j-1)//2)
                                   for j in range(1,k))
    return out


def reciprocal_graph_coeffs(n: int) -> list[int]:
    # Exponential-series reciprocal, independently checked by multiplication.
    b=[1]
    for k in range(1,n+1):
        b.append(-sum(comb(k,j)*2**(j*(j-1)//2)*b[k-j] for j in range(1,k+1)))
    for k in range(1,n+1):
        assert sum(comb(k,j)*2**(j*(j-1)//2)*b[k-j] for j in range(k+1))==0
    return b


def mpf(q):
    return mp.mpf(str(sp.N(q,110)))


def scientific(x, digits=5):
    return mp.nstr(x,digits,min_fixed=0,max_fixed=0)


def main():
    report=[]
    results={}
    qcat=[(-1)**(j+1)*(sp.bernoulli(j+1,1)*(sp.Rational(1,2)**j-1)-
                       sp.bernoulli(j+1,2))/sp.Integer(j*(j+1)) for j in range(1,7)]
    acat=exp_coefficients(qcat,6)
    assert qcat[:4]==[-sp.Rational(9,8),sp.Rational(1,2),-sp.Rational(21,64),sp.Rational(1,4)]
    assert acat[:4]==[1,-sp.Rational(9,8),sp.Rational(145,128),-sp.Rational(1155,1024)]
    results['Catalan_log']=[str(v) for v in qcat]
    results['Catalan_amplitude']=[str(v) for v in acat]
    for kind in ['motzkin_plus','motzkin_minus','delannoy','schroder']:
        vals=endpoint_coefficients(kind,4)
        results[kind]=[str(v) for v in vals]
    assert endpoint_coefficients('motzkin_plus',2)==[1,-sp.Rational(39,16),sp.Rational(2665,512)]
    inv= involution_coefficients(5)
    assert inv[:3]==[1,sp.Rational(7,24),-sp.Rational(119,1152)]
    results['involution_amplitude']=[str(v) for v in inv]
    results['involution_log']=[str(v) for v in log_coefficients(inv,5)]
    hc=[]
    for m in range(1,6):
        q=[-(2*m-1)*sp.bernoulli(2*j,sp.Rational(1,2))/sp.Integer(2*j) for j in range(1,m+1)]
        hc.append(sp.factor(-exp_coefficients(q,m)[m]/sp.Integer(2*m-1)))
    assert hc[:2]==[-sp.Rational(1,24),sp.Rational(3,640)]
    results['harmonic_inverse']=[str(v) for v in hc]
    b=reciprocal_graph_coeffs(9)
    assert b[:5]==[1,-1,0,-2,-24]
    results['graph_reciprocal_b']=b
    # Gaussian finite sum identity with involution recurrence.
    iv=[1,1]
    for n in range(2,31):iv.append(iv[-1]+(n-1)*iv[-2])
    for n in range(31):
        assert iv[n]==sum(factorial(n)//(2**j*factorial(j)*factorial(n-2*j)) for j in range(n//2+1))
    report.append('All exact assertions passed.')
    report.append(json.dumps(results,indent=2))
    # Catalan inverse: compare the W core and three explicitly derived corrections.
    a=mp.log(4)
    catrows=[]
    for n in [20,100,1000]:
        y=mp.binomial(2*n,n)/(n+1)
        X=-mp.mpf(3)/(2*a)*mp.lambertw(-2*a/3*(1/(mp.sqrt(mp.pi)*y))**(mp.mpf(2)/3),-1)
        ds=[mp.mpf(9)/(8*a),mp.mpf(27)/(16*a*a)-1/(2*a),
            mp.mpf(81)/(32*a**3)-mp.mpf(129)/(64*a*a)+mp.mpf(21)/(64*a)]
        xs=X+sum(ds[j]/X**(j+1) for j in range(3))
        catrows.append((n,scientific(abs(X-n)),scientific(abs(xs-n))))
    results['catalan_inverse_errors']=catrows
    # Involutions: forward positive-saddle relative error, and inverse to 3 displayed orders.
    invrows=[]
    for n in [100,400,1600]:
        val=mp.mpf(sum(factorial(n)//(2**j*factorial(j)*factorial(n-2*j)) for j in range(n//2+1)))
        lead=mp.exp(mp.mpf(n)/2*(mp.log(n)-1)+mp.sqrt(n)-mp.mpf(1)/4)/mp.sqrt(2)
        app=lead*sum(mpf(inv[j])*mp.mpf(n)**(-mp.mpf(j)/2) for j in range(6))
        L=mp.log(val*mp.sqrt(2))+mp.mpf(1)/4
        X=2*L/mp.lambertw(2*L/mp.e)
        ell=mp.log(X)
        z0=-2/ell
        z1=2/ell**2-2/ell**3
        z2=-mp.mpf(7)/(12*ell)-1/ell**3+mp.mpf(14)/(3*ell**4)-4/ell**5
        appinv=X+mp.sqrt(X)*z0+z1+z2/mp.sqrt(X)
        invrows.append((n,scientific(abs(app/val-1)),scientific(abs(appinv-n))))
    results['involution_errors']=invrows
    # Connected graph inverse and forward sectors, with exact integer enumeration.
    cg=connected_graphs(80)
    grows=[]
    for n in [12,20,40]:
        y=mp.mpf(cg[n]); aa=mp.log(2)
        X=(1+mp.sqrt(1+8*mp.log(y)/aa))/2
        p=aa*(X-mp.mpf('0.5'))
        d1=2*X/p
        d2=(2*X*X-2*(aa*X-1)*d1-aa*d1*d1/2)/p
        v1=X+d1*2**(-X)
        v2=v1+d2*2**(-2*X)
        grows.append((n,scientific(abs(X-n)),scientific(abs(v1-n)),scientific(abs(v2-n))))
    results['graph_inverse_errors']=grows
    # Harmonic inverse, using the exact digamma interpolation.
    hrows=[]
    for n in [10,100,1000]:
        y=mp.harmonic(n); X=mp.exp(y-mp.euler)
        app=X-mp.mpf('0.5')+sum(mpf(hc[j])*X**(-2*j-1) for j in range(3))
        hrows.append((n,scientific(abs(app-n))))
    results['harmonic_inverse_errors']=hrows
    # Inverse S(x,3) by the closed multivariate formula, total degree <= 6.
    srows=[]
    beta=mp.log(mp.mpf(3)/2)/mp.log(3)
    for n in [10,20,50]:
        y=(mp.mpf(3)**n-3*mp.mpf(2)**n+3)/6
        X=mp.log(6*y)/mp.log(3)
        T=(6*y)**(-beta); U=1/(6*y)
        correction=mp.mpf(0)
        for M in range(1,7):
            for m in range(M+1):
                j=M-m
                correction-=mp.factorial(M-1)/(mp.factorial(m)*mp.factorial(j))*\
                    mp.binomial(beta*m+j-1,M-1)*(-3*T)**m*(3*U)**j/mp.log(3)
        srows.append((n,scientific(abs(X-n)),scientific(abs(X+correction-n))))
    results['stirling2_inverse_errors']=srows
    report.append('\nNUMERICAL CHECKS (absolute inverse errors):')
    for key in ['catalan_inverse_errors','involution_errors','graph_inverse_errors','harmonic_inverse_errors','stirling2_inverse_errors']:
        report.append(key+': '+str(results[key]))
    root=Path(__file__).resolve().parent
    (root/'verification_results.json').write_text(json.dumps(results,indent=2)+'\n')
    (root/'verification_report.txt').write_text('\n'.join(report)+'\n')
    print('\n'.join(report))

if __name__=='__main__':
    main()
