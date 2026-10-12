#!/usr/bin/env python3
"""Finite exact tests and independent high-precision diagnostics.

No network access. Results are diagnostics, not interval certificates or a
proof-assistant formalization. The article supplies the all-order proofs.
Run from any directory: python verification/verify.py --part all
Use --output-dir to avoid overwriting the packaged data.
"""
from __future__ import annotations
import argparse
import functools
import json
import math
import platform
import time
from fractions import Fraction as Q
from pathlib import Path
from typing import Sequence

import mpmath as mp
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]

# Truncated coefficient arithmetic, implemented separately from SymPy.
def add(a, b, n):
    return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
            for i in range(n+1)]

def scale(a, c, n):
    return [(a[i] if i < len(a) else 0)*c for i in range(n+1)]

def mul(a, b, n):
    out = [0]*(n+1)
    for i in range(min(n+1, len(a))):
        for j in range(min(n-i+1, len(b))):
            out[i+j] += a[i]*b[j]
    return out

def power(a, k, n):
    if k < 0:
        return power(reciprocal(a, n), -k, n)
    out = [1]+[0]*n
    while k:
        if k & 1:
            out = mul(out, a, n)
        a = mul(a, a, n)
        k >>= 1
    return out

def reciprocal(a, n):
    if not a or a[0] == 0:
        raise ValueError('Nonzero constant coefficient required')
    out = [1/a[0]]+[0]*n
    for j in range(1, n+1):
        out[j] = -sum(a[k]*out[j-k] for k in range(1, min(j+1,len(a))))/a[0]
    return out

def compose(a, u, n):
    if u[0] != 0:
        raise ValueError('Composition expects zero constant term')
    out = [0]*(n+1)
    for c in reversed(a):
        out = mul(out, u, n)
        out[0] += c
    return out

def log_one_plus(u, n):
    return compose([0]+[Q((-1)**(j+1),j) for j in range(1,n+1)],u,n)

def phi_series(m, d, w, n):
    u = [0, Q(1)]+[0]*max(0,n-1)
    one_u = add([Q(1)], u, n)
    bracket = add([Q(1)], scale(log_one_plus(u,n),-w,n), n)
    out = mul(power(one_u,m,n),power(bracket,d,n),n)
    out[0] -= 1
    return out

def residual(u, m, d, w, b, n):
    one_u = add([1],u,n)
    bracket = add([1],scale(log_one_plus(u,n),-w,n),n)
    v_one_u = [0]+one_u[:n]
    correction = scale(compose([0]+list(b[1:n+1]),v_one_u,n),w**d,n)
    out = mul(power(one_u,m,n),add(power(bracket,d,n),correction,n),n)
    out[0] -= 1
    return out

def inverse_recursive(m, d, w, b, n):
    alpha = m-d*w
    if alpha == 0:
        raise ValueError('The auxiliary fold alpha=0 is excluded')
    u = [Q(0)]*(n+1)
    for j in range(1,n+1):
        u[j] = -residual(u,m,d,w,b,j)[j]/alpha
    return u

def inverse_lagrange(m, d, w, b, n):
    ph = phi_series(m,d,w,n+1)
    quotient = reciprocal(ph[1:],n)
    out = [0]*(n+1)
    for j in range(1,n+1):
        for k in range(1,j+1):
            bk = power(b,k,j)[j]
            degree = k-1
            factor = [Q(math.comb(m*k+j,l)) for l in range(degree+1)]
            coeff = mul(factor,power(quotient,k,degree),degree)[degree]
            out[j] += (-w**d)**k * bk * coeff / k
    return out


def exact_checks(outdir: Path):
    start=time.monotonic(); count=0; groups={}
    def check(test, group):
        nonlocal count
        if not test:
            raise AssertionError(f'Exact test failed: {group}')
        count += 1; groups[group]=groups.get(group,0)+1
    x,L,a=sp.symbols('x L a')
    # Pure-log projection and its general finite-difference law.
    for d in range(1,13):
        h=d-1
        centered=sum((-1)**j*sp.binomial(h,j)*
                     (L-(sp.Rational(j)-sp.Rational(h,2))*a)**d for j in range(h+1))
        check(sp.expand(centered-sp.factorial(d)*a**h*L)==0,'centered_log_projection')
        for h in range(d+2):
            left=sp.expand(sum((-1)**j*sp.binomial(h,j)*(L-j*a)**d for j in range(h+1)))
            from sympy.functions.combinatorial.numbers import stirling
            right=sp.factorial(h)*sum(sp.binomial(d,k)*(-1)**(k+h)*
                     stirling(k,h,kind=2)*a**k*L**(d-k) for k in range(h,d+1))
            check(sp.expand(left-right)==0,'finite_difference_stirling')
    for n in range(1,11):
        mat=sp.Matrix([[sp.Integer(j)**k for j in range(n)] for k in range(n)])
        det=sp.prod(j-i for i in range(n) for j in range(i+1,n))
        check(mat.det()==det and det!=0,'minimal_node_vandermonde')
    # Scalar normalizer recurrence checked against an independent product.
    # Formal Gamma reciprocal coefficients are generated from its logarithm.
    degree=7
    g=sp.symbols('g0:'+str(degree+1))
    gamma_inverse=[sp.Integer(1)]+list(g[1:])
    for m in range(0,9):
        prod=[Q(1)]+[Q(0)]*degree
        for j in range(1,m+1):
            prod=mul(prod,[Q(1),Q(1,j)],degree)
        via_product=mul(prod,gamma_inverse,degree)
        e=sp.expand(sp.prod(1+x/sp.Integer(j) for j in range(1,m+1)))
        for j in range(degree+1):
            expected=sum(e.coeff(x,k)*gamma_inverse[j-k] for k in range(j+1))
            check(sp.expand(via_product[j]-expected)==0,'normalizer_product_coefficients')
    # Bernoulli/Hurwitz tail coefficients, including exact half-shift parity.
    bernoulli_data=[]
    for m in range(1,7):
        for n in range(1,21):
            z=-sp.bernoulli(n,sp.Rational(1,2))/n
            b=sp.Rational((-1)**n*math.factorial(m),math.factorial(m+n))*z
            if n%2:
                check(b==0,'half_shift_even_tail')
            if n==2:
                check(b==sp.Rational(1,24*(m+1)*(m+2)),'half_shift_first_nonzero')
            if m<=3 and n<=10:
                bernoulli_data.append({'m':m,'n':n,'b_half_r0':str(b)})
        z=-sp.bernoulli(1,1)
        check(-z/(m+1)==sp.Rational(1,2*(m+1)),'ordinary_shift_first_coefficient')
    # Independent rational recurrence vs finite Lagrange coefficient formula.
    n=7
    b=[Q(0)]+[Q((-1)**(j+1),j+2) for j in range(1,n+1)]
    for m in (1,2,4):
        for d in (1,2,3,5):
            for w in (Q(1,11),Q(2,13)):
                rec=inverse_recursive(m,d,w,b,n)
                lag=inverse_lagrange(m,d,w,b,n)
                for j in range(1,n+1):
                    check(rec[j]==lag[j], 'two_independent_inverse_compilers')
                check(all(c==0 for c in residual(rec,m,d,w,b,n)), 'inverse_exact_residual')
                alpha=m-d*w
                beta=Q(m*(m-1),2)+d*(Q(1,2)-m)*w+Q(d*(d-1),2)*w*w
                c1=-w**d*b[1]/alpha
                c2=-w**d*b[2]/alpha+w**(2*d)*b[1]**2*((m+1)*alpha-beta)/alpha**3
                check(rec[1]==c1,'displayed_C1')
                check(rec[2]==c2,'displayed_C2')
    # Support is inherited under analytic inversion.
    for gval in (2,3,4):
        n=12
        bb=[Q(0)]+[Q(1,j+1) if j%gval==0 else Q(0) for j in range(1,n+1)]
        rec=inverse_recursive(2,3,Q(1,11),bb,n)
        for j in range(1,n+1):
            if j%gval:
                check(rec[j]==0,'inverse_sector_support')
    # Universal deepest-pole combinatorics.
    for n in range(1,31):
        check(Q(math.comb(2*n-2,n-1),n)==Q(math.comb(2*n,n),2*(2*n-1)),
              'catalan_deepest_pole')
    # Raw derivative sign audit. r=1 gives a strict polynomial discrepancy.
    gamma,z2=sp.symbols('gamma zeta2', real=True)
    for m in range(0,7):
        H=sp.harmonic(m); H2=sp.harmonic(m,2)
        a2=((gamma-H)**2+z2+H2)/2
        check(sp.expand(2*a2-((gamma-H)**2+z2+H2))==0,'source_sign_discrepancy')
    result={'kind':'finite exact algebra, not all-order formalization',
        'assertions_passed':count,'groups':groups,'seconds':round(time.monotonic()-start,3),
        'python':platform.python_version(),'sympy':sp.__version__}
    (outdir/'exact_results.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    (outdir/'bernoulli_coefficients.json').write_text(json.dumps(bernoulli_data,indent=2)+'\n',encoding='utf-8',newline='\n')
    return result

# High-precision routines.
@functools.lru_cache(maxsize=None)
def zeta_derivative(s: int, a: str, order: int):
    aa=mp.mpf(a)
    return mp.zeta(s,aa) if order==0 else mp.diff(lambda u:mp.zeta(u,aa),mp.mpf(s),order)

@functools.lru_cache(maxsize=None)
def dcoeff(m: int, n: int):
    # log D_m(e)=(H_m-gamma)e - sum_{k>=2}(zeta(k)+(-1)^k H_m^(k))e^k/k
    c=[mp.mpf(0)]*(n+1)
    if n:
        c[1]=mp.harmonic(m)-mp.euler
    for k in range(2,n+1):
        h=mp.fsum(mp.mpf(j)**(-k) for j in range(1,m+1))
        c[k]=-(mp.zeta(k)+(-1)**k*h)/k
    vals=[mp.mpf(1)]+[mp.mpf(0)]*n
    for j in range(1,n+1):
        vals[j]=mp.fsum(k*c[k]*vals[j-k] for k in range(1,j+1))/j
    return tuple(vals)

@functools.lru_cache(maxsize=None)
def counterterm(m: int, r: int, a: str):
    ds=dcoeff(m,r+1)
    return ds[r+1]+mp.fsum(ds[j]*(-1)**(r-j)*mp.stieltjes(r-j,mp.mpf(a))/mp.factorial(r-j)
                         for j in range(r+1))

@functools.lru_cache(maxsize=None)
def tail_coeffs(m: int, r: int, a: str, n: int):
    ds=dcoeff(m,r)
    vals=[mp.mpf(0)]
    for k in range(1,n+1):
        jet=mp.fsum(ds[j]*zeta_derivative(1-k,a,r-j)/mp.factorial(r-j) for j in range(r+1))
        vals.append((-1)**(k+r)*(r+1)*mp.factorial(r)*mp.factorial(m)/mp.factorial(m+k)*jet)
    return tuple(vals)

def psi_jet_direct(t, s: int, a: str, r: int):
    aa=mp.mpf(a)
    # A direct finite exponential sum; truncation chosen far below test tolerance.
    # This is a diagnostic, not an outward-rounded certified tail enclosure.
    cutoff=int(mp.ceil((mp.mp.dps+20)*mp.log(10)/mp.re(t)))
    return mp.fsum(mp.exp(-(n+aa)*t)*(-mp.log(n+aa))**r/(n+aa)**s for n in range(cutoff))

def jet_direct(t, m: int, r: int, a: str):
    ds=dcoeff(m,r)
    terms=[]
    for j in range(r+1):
        order=r-j
        val=psi_jet_direct(t,m+1,a,order)
        val-=mp.fsum(zeta_derivative(m+1-k,a,order)*(-t)**k/mp.factorial(k) for k in range(m))
        terms.append(ds[j]*val/mp.factorial(order))
    return (-1)**r*(r+1)*mp.factorial(r)*(
            (-1)**m*mp.factorial(m)*mp.fsum(terms)-t**m*counterterm(m,r,a))

def jet_tail(t,m,r,a,n=40):
    bs=tail_coeffs(m,r,a,n)
    return t**m*((-mp.log(t))**(r+1)+mp.fsum(bs[k]*t**k for k in range(1,n+1)))

def numerical_checks(outdir: Path):
    start=time.monotonic();mp.mp.dps=80
    rows=[]
    def record(name, actual, expected, tolerance=mp.mpf('1e-52'), **params):
        error=abs(actual-expected)/(1+abs(expected))
        if not error<tolerance:
            raise AssertionError(f'{name}: relative-scaled residual {error} >= {tolerance}')
        rows.append({'test':name,**params,'scaled_residual':mp.nstr(error,12),
                     'tolerance':str(tolerance)})
    # Direct defining exponential sums vs normally convergent Hurwitz tails.
    for m in (1,2,4):
        for r in (0,1,2):
            for astr in ('1','0.5'):
                t=mp.mpf('0.12')
                record('direct_spectral_sum_vs_normal_form',jet_direct(t,m,r,astr),
                       jet_tail(t,m,r,astr),m=m,r=r,a=astr,t=str(t))
    for r in (0,1,2):
        t=mp.mpf('0.1');astr='0.33333333333333333333333333333333333333333333333333333333333333333333333333333333'
        record('non_dyadic_shift',jet_direct(t,2,r,astr),jet_tail(t,2,r,astr),m=2,r=r,a='1/3 to working precision')
    # Explicit dilogarithmic first jet.
    t=mp.mpf('0.1')
    li2=mp.polylog(2,mp.exp(-t))
    deriv=psi_jet_direct(t,2,'1',1)
    explicit=2*(deriv-mp.diff(mp.zeta,2)+(1-mp.euler)*(li2-mp.zeta(2)))-t*(mp.euler**2+mp.zeta(2)+2*mp.stieltjes(1))
    record('displayed_dilog_first_jet',explicit,jet_tail(t,1,1,'1'))
    # Centered filter, evaluated directly on the special functions.
    for d in (2,3):
        m=1;r=d-1;aa=mp.log(2);h=d-1;t=mp.mpf('0.07')
        lhs=mp.fsum((-1)**j*mp.binomial(h,j)*mp.exp(-m*(j-mp.mpf(h)/2)*aa)*
             jet_direct(t*mp.exp((j-mp.mpf(h)/2)*aa),m,r,'1') for j in range(d))/(mp.factorial(d)*aa**h)
        bs=tail_coeffs(m,r,'1',40)
        right=t**m*(-mp.log(t)+mp.fsum(bs[n]*(-2*mp.sinh(n*aa/2))**h/
                           (mp.factorial(d)*aa**h)*t**n for n in range(1,41)))
        record('centered_filter_direct',lhs,right,d=d)
    # Rational-shift Fourier identity, no derivative libraries used for RHS.
    for q in (2,3,5):
        for p in range(1,q+1):
            t=mp.mpf('0.22');s=mp.mpf('2.25')
            lhs=mp.fsum(mp.exp(-(n+mp.mpf(p)/q)*t)/(n+mp.mpf(p)/q)**s for n in range(1200))
            rhs=q**(s-1)*mp.fsum(mp.exp(-2j*mp.pi*j*p/q)*
                          mp.polylog(s,mp.exp(-t/q+2j*mp.pi*j/q)) for j in range(q))
            record('finite_fourier_hurwitz_polylog',lhs,rhs,p=p,q=q)
    # Analytic inverse: solve a separately evaluated high-order tail, then
    # compare finite reversion coefficients from the Lagrange engine.
    inverses=[]
    for m,r,astr in ((1,0,'1'),(2,0,'0.5'),(1,1,'0.5'),(2,2,'1')):
        d=r+1;bs=tail_coeffs(m,r,astr,40)
        for ll in (8,12,18):
            L=mp.mpf(ll);v=mp.exp(-L);w=1/L;y=v**m*L**d
            bb=list(bs[:9]);u=inverse_lagrange(m,d,w,bb,8)
            approx=v*(1+mp.fsum(u[n]*v**n for n in range(1,9)))
            func=lambda t: t**m*((-mp.log(t))**d+mp.fsum(bs[n]*t**n for n in range(1,41)))-y
            root=mp.findroot(func,(v*(1-mp.mpf('0.001')),v*(1+mp.mpf('0.001'))),solver='secant',tol=mp.mpf('1e-75'))
            # 8 correction sectors, with a v^9 error in the relative inverse.
            err=abs(approx/root-1)
            if not err < 100*v**9:
                raise AssertionError(f'inverse remainder unexpectedly large: {m,r,astr,ll,err}')
            core=mp.exp(mp.mpf(d)/m*mp.lambertw(-mp.mpf(m)/d*y**(mp.mpf(1)/d),-1))
            record('Lambert_core',core,v,m=m,d=d,L=ll)
            inverses.append({'m':m,'r':r,'a':astr,'L':ll,'relative_inverse_error':mp.nstr(err,12),
                'relative_equation_residual':mp.nstr(abs(func(approx))/y,12),
                'estimated_first_correction':mp.nstr(u[1]*v,12)})
    # Verified version-specific sign error in the author-hosted MTW1.pdf.
    # Their k=1, derivative order 1, z=e^-1 lies within the stated domain.
    t=mp.mpf(1);L=mp.mpf(0);k=1
    a2=((mp.euler-1)**2+mp.zeta(2)+1)/2
    zeta_tail=mp.fsum(zeta_derivative(2-n,'1',1)*(-t)**n/mp.factorial(n)
                     for n in range(101) if n!=1)
    correct=zeta_tail+(-mp.stieltjes(1)-a2)*(-t)
    wrong=zeta_tail+(-mp.stieltjes(1)+a2)*(-t)
    actual=psi_jet_direct(t,2,'1',1)
    record('source_52_corrected_minus',actual,correct,tolerance=mp.mpf('1e-68'))
    audit={'source':'https://carmamaths.org/jon/MTW1.pdf','pdf_pages':[12,13],
           'equations':[48,49,50,52,54], 'scope':'author-hosted 29-page version inspected; not a claim about every edition',
           'k':1,'derivative_order':1,'z':'exp(-1)',
           'direct_value':mp.nstr(actual,60),'corrected_value':mp.nstr(correct,60),
           'printed_plus_value':mp.nstr(wrong,60),'printed_minus_correct':mp.nstr(wrong-correct,60),
           'exact_discrepancy':'-((EulerGamma-1)^2 + zeta(2) + 1)'}
    result={'kind':'80-digit floating-point diagnostics, not interval certificates',
       'comparisons_passed':len(rows),'inverse_comparisons_passed':len(inverses),
       'seconds':round(time.monotonic()-start,3),'mpmath':mp.__version__,
       'rows':rows,'inverse_rows':inverses}
    (outdir/'numerical_results.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    (outdir/'source_sign_audit.json').write_text(json.dumps(audit,indent=2)+'\n',encoding='utf-8',newline='\n')
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--part',choices=['all','exact','numerical'],default='all')
    parser.add_argument('--output-dir',type=Path,default=ROOT/'data')
    args=parser.parse_args(); args.output_dir.mkdir(parents=True,exist_ok=True)
    summary={}
    if args.part in ('all','exact'):
        summary['exact']=exact_checks(args.output_dir)
        print(json.dumps(summary['exact'],indent=2),flush=True)
    if args.part in ('all','numerical'):
        r=numerical_checks(args.output_dir)
        summary['numerical']={k:v for k,v in r.items() if k not in ('rows','inverse_rows')}
        print(json.dumps(summary['numerical'],indent=2),flush=True)
    (args.output_dir/f'run_{args.part}.json').write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8',newline='\n')

if __name__=='__main__':
    main()
