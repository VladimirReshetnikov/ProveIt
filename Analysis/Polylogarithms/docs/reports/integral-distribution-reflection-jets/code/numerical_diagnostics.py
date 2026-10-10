#!/usr/bin/env python3
"""Optional high-precision diagnostics, NOT interval or equality certificates.

The exact proof is the polynomial row combination. Mellin quadrature supplies
an independent mathematical representation for two displayed specializations.
"""
from pathlib import Path
import json
import mpmath as mp

ROOT=Path(__file__).resolve().parents[1]
if not __debug__:
    raise RuntimeError('Run without -O: the regression suite uses assertions.')

def z(q,a):return mp.exp(2j*mp.pi*a/q)
def L(q,a,s):return mp.polylog(s,z(q,a))
def identity15(s):
    left=L(15,8,s)-sum(L(15,a,s) for a in (1,4,7,6,12))
    left-=(mp.power(3,1-s)+1)*L(5,3,s)
    left-=(mp.power(5,1-s)+1)*L(3,2,s)
    right=mp.log(15) if s==1 else -mp.expm1((1-s)*mp.log(15))*mp.zeta(s)
    return left,right

def mellin15(s):
    terms=[(1,z(15,8))]+[(-1,z(15,a)) for a in (1,4,7,6,12)]
    terms += [(-(mp.power(3,1-s)+1),z(5,3)),
              (-(mp.power(5,1-s)+1),z(3,2))]
    def integrand(t):
        u=mp.exp(-t)
        return t**(s-1)*sum(c*w*u/(1-w*u) for c,w in terms)
    return mp.quad(integrand,[0,1,4,12,mp.inf])/mp.gamma(s)

def jet15(n):
    # Differentiate the Mellin representation analytically, not a library
    # polylogarithm implementation by very small finite differences in order.
    euler=mp.euler
    def P(x):
        y=x+euler
        if n==0:return mp.mpf(1)
        if n==1:return y
        if n==2:return y*y-mp.zeta(2)
        if n==3:return y**3-3*mp.zeta(2)*y+2*mp.zeta(3)
        raise ValueError('this diagnostic implements orders 0 through 3')
    unweighted=[z(15,a) for a in (1,4,7,6,12)]
    z8,z3,z5=z(15,8),z(5,3),z(3,2)
    def integrand(u):
        v=mp.exp(-u)
        K=lambda w:w*v/(1-w*v)
        ell=mp.log(u)
        return (P(ell)*(K(z8)-sum(K(w) for w in unweighted)-K(z3)-K(z5))
                -P(ell-mp.log(3))*K(z3)-P(ell-mp.log(5))*K(z5))
    left=mp.quad(integrand,[0,mp.mpf('0.25'),1,4,12,mp.inf])
    ell=mp.log(15)
    right=(-1)**n*(ell**(n+1)/(n+1)-sum(mp.binomial(n,j)*ell**j*mp.stieltjes(n-j)
                                                   for j in range(1,n+1)))
    return left,right

def text(x):return mp.nstr(x,16)

def main():
    records=[]
    for dps in (65,95):
        with mp.workdps(dps):
            samples=[mp.mpf(2),mp.mpf(3),mp.mpf('0.5'),mp.mpc('1.2','0.4'),mp.mpf(-2),mp.mpf(1)]
            for s in samples:
                left,right=identity15(s)
                err=abs(left-right)
                assert err<mp.mpf(10)**(-dps+8)
                records.append({'kind':'level15_spectral_identity','dps':dps,
                                's':str(s),'absolute_residual':text(err)})
            for n in range(4) if dps==65 else ():
                left,right=jet15(n)
                err=abs(left-right)
                assert err<mp.mpf(10)**(-dps+8)
                records.append({'kind':'level15_jet_differentiated_Mellin','dps':dps,'jet_order':n,
                                'absolute_residual':text(err)})
    with mp.workdps(65):
        for s in (mp.mpf(1),mp.mpf(2)):
            direct,right=identity15(s)
            integral=mellin15(s)
            err=abs(integral-right)
            assert err<mp.mpf('1e-57')
            records.append({'kind':'independent_Mellin_quadrature','dps':65,'s':str(s),
                            'absolute_residual':text(err),
                            'difference_from_polylog_engine':text(abs(integral-direct))})
    out={'status':'PASS','evidence':'non-rigorous floating-point diagnostics; no interval enclosure',
         'mpmath_version':mp.__version__,'checks':records}
    (ROOT/'logs/numerical_diagnostics.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))

if __name__=='__main__':main()
