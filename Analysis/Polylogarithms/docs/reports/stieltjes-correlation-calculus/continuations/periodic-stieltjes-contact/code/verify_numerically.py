#!/usr/bin/env python3
"""Independent coordinate finite-part quadrature and Fourier/contact checks.

The local integrator uses the Hurwitz shift expansion, NOT the contact kernel.
Results are high-precision diagnostics, not interval certificates.
"""
from __future__ import annotations
import argparse, json, math, platform
from functools import lru_cache
from pathlib import Path
import mpmath as mp
ROOT = Path(__file__).resolve().parents[1]


def run(dps: int = 55, terms: int = 225) -> dict:
    if dps < 30 or terms < 100:
        raise ValueError('Use at least 30 digits and 100 Taylor terms.')
    mp.mp.dps = dps
    z = [mp.mpf(0)] * (terms + 1)
    zp = [mp.mpf(0)] * (terms + 1)
    harmonic = [mp.mpf(0)] * (terms + 1)
    a = [[mp.mpf(0)] * (terms + 1) for _ in range(2)]
    a[0][0], a[1][0] = mp.euler, mp.stieltjes(1)
    for j in range(1, terms + 1):
        harmonic[j] = harmonic[j-1] + mp.mpf(1)/j
        z[j] = mp.zeta(j+1)
        zp[j] = mp.diff(mp.zeta, j+1)
        a[0][j] = (-1)**j*z[j]
        a[1][j] = (-1)**(j+1)*(harmonic[j]*z[j]+zp[j])
    coeffs = {}
    for m in range(2):
        for p in range(5):
            coeffs[m,p] = [a[m][j]*mp.factorial(j)/mp.factorial(j-p)
                           for j in range(p, terms+1)]

    def smooth(m: int, p: int, y):
        return mp.polyval(list(reversed(coeffs[m,p])), y)

    def value(m: int, p: int, x):
        if m == 0:
            return -mp.polygamma(p,x)
        if x <= mp.mpf('.5'):
            return ((-1)**p*mp.factorial(p)*x**(-p-1)
                    *(mp.log(x)-harmonic[p]) + smooth(m,p,x))
        return smooth(m,p,x-1)

    def primitive_power(e: int, b):
        return mp.log(b) if e == -1 else b**(e+1)/(e+1)

    def primitive_log(e: int, b):
        if e == -1:
            return mp.log(b)**2/2
        h = e+1
        return b**h*(mp.log(b)/h-mp.mpf(1)/h**2)

    def moment(m: int, p: int, k: int, b=mp.mpf('.2')):
        """FP integral gamma_m^(p)(x) exp(-2 pi i k x), direct coordinate."""
        omega = 2j*mp.pi*k
        local_terms = 95
        ec = [(-omega)**j/mp.factorial(j) for j in range(local_terms+1)]
        singular = mp.mpc(0)
        for j,c in enumerate(ec):
            e = j-p-1
            integ = primitive_power(e,b)
            if m:
                integ = primitive_log(e,b)-harmonic[p]*integ
            singular += (-1)**p*mp.factorial(p)*c*integ
        # Product of the smooth Hurwitz tail with the exponential, integrated exactly.
        regular = mp.mpc(0)
        co = coeffs[m,p]
        for degree in range(local_terms+1):
            c = mp.fsum(co[j]*ec[degree-j] for j in range(degree+1))
            regular += c*b**(degree+1)/(degree+1)
        bulk = mp.quad(lambda x:value(m,p,x)*mp.exp(-omega*x), [b,mp.mpf('.5'),1])
        return singular+regular+bulk

    def predicted(m: int,p: int,k: int):
        if k == 0:
            return mp.mpc(0)
        omega=2j*mp.pi*k
        L=mp.euler+mp.log(omega)
        if m == 0:
            return omega**p*(harmonic[p]-L)
        e2=(harmonic[p]**2-mp.fsum(mp.mpf(1)/j**2 for j in range(1,p+1)))/2
        return omega**p*((L**2+mp.zeta(2))/2-e2)

    records=[]
    tol=mp.mpf('2e-38')
    def record(group,params,actual,expected,tolerance=tol):
        residual=abs(actual-expected)/(1+abs(expected))
        row={'group':group,'parameters':params,
             'actual':mp.nstr(actual,48),'expected':mp.nstr(expected,48),
             'relative_residual':mp.nstr(residual,8),
             'tolerance':str(tolerance),'passed':bool(residual<tolerance)}
        records.append(row)
        if not row['passed']:
            raise AssertionError(row)

    moments={}
    for m in range(2):
        for p in range(5):
            for k in [0,1,2]:
                x=moment(m,p,k)
                moments[m,p,k]=x
                record('coordinate_fourier_moment',{'m':m,'p':p,'k':k},x,predicted(m,p,k))
    for p in range(5):
        for q in range(5-p):
            r=p+q
            H=lambda n:harmonic[n]
            H2=lambda n:mp.fsum(mp.mpf(1)/j**2 for j in range(1,n+1))
            delta=(-1)**p*(2*mp.zeta(2)-H2(r)+(H(r)-H(p))*(H(r)-H(q)))
            for k in [1,2]:
                conv=mp.conj(moments[0,p,k])*moments[0,q,k]
                J=((-1)**p*(H(p)*moments[0,r,k]+moments[1,r,k])
                   +(-1)**q*(H(q)*mp.conj(moments[0,r,k])+mp.conj(moments[1,r,k])))
                record('collision_contact',{'p':p,'q':q,'k':k},
                       conv-J,delta*(2j*mp.pi*k)**r)
    for m,p,k in [(0,4,2),(1,0,1),(1,3,1)]:
        x=moment(m,p,k,mp.mpf('.15'))
        record('changed_split',{'m':m,'p':p,'k':k,'split':'0.15'},x,moments[m,p,k])
    for k in [1,2]:
        weight=lambda x:4*mp.sin(mp.pi*k*x)**4
        I0=mp.quad(lambda x:weight(x)*mp.zeta(3,x),[0,mp.mpf('.25'),mp.mpf('.5'),1])
        I1=mp.quad(lambda x:weight(x)*mp.diff(lambda s:mp.zeta(s,x),3),
                   [0,mp.mpf('.25'),mp.mpf('.5'),1])
        L=mp.euler+mp.log(2*mp.pi*k)
        record('ordinary_zeta_integral',{'s':3,'jet':0,'k':k},I0,4*mp.pi**2*k*k*mp.log(2))
        record('ordinary_zeta_integral',{'s':3,'jet':1,'k':k},I1,
               4*mp.pi**2*k*k*mp.log(2)*(L-mp.mpf('1.5')+mp.log(2)/2))
    # Independent ordinary integral of digamma with a vanishing trigonometric weight.
    for k in [1,3]:
        I=mp.quad(lambda x:-2*mp.sin(mp.pi*k*x)**2*mp.digamma(x),[0,mp.mpf('.5'),1])
        record('ordinary_digamma_integral',{'k':k},I,mp.euler+mp.log(2*mp.pi*k))
    result={'status':'PASS','precision_dps':dps,'smooth_taylor_terms':terms,
            'local_product_terms':95,'python':platform.python_version(),
            'mpmath':mp.__version__,'count':len(records),
            'maximum_relative_residual':mp.nstr(max(mp.mpf(x['relative_residual']) for x in records),8),
            'note':'Floating-point and truncation diagnostics; not interval certification.',
            'checks':records}
    (ROOT/'data'/'numerical_checks.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='checks'},indent=2))
    return result

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--dps',type=int,default=55)
    parser.add_argument('--terms',type=int,default=225)
    args=parser.parse_args()
    run(args.dps,args.terms)
