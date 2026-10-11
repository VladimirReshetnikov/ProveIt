#!/usr/bin/env python3
"""Independent finite checks and stable quadrature for Gamma normalizers.

No proof-assistant or interval verification is claimed. The two integral
evaluators use different integrands: analytic Gamma-ratio coefficients
on [0,1], and the completed logarithmic kernel on (0,infinity).
"""
from __future__ import annotations

import argparse
import json
from math import comb, factorial
from pathlib import Path

import mpmath as mp
import sympy as sp


def integer_partitions(n, minimum=1):
    if n == 0:
        yield ()
    else:
        for first in range(minimum,n+1):
            for rest in integer_partitions(n-first,first):
                yield (first,)+rest


def elementary(n, k):
    if k < 0 or k > n:
        return sp.S.Zero
    a=[sp.S.One]+[sp.S.Zero]*k
    for j in range(1,n+1):
        for r in range(min(j,k),0,-1):
            a[r] += a[r-1]/j
    return a[k]


def exact_checks():
    maximum=8
    t=sp.symbols('t')
    H=sp.symbols('H1:9')
    Z={j:sp.Symbol('zeta_'+str(j)) for j in range(2,maximum+2)}
    h=[sp.S.One]
    for m in range(1,maximum+1):
        h.append(sp.expand(sum(H[r-1]*h[m-r] for r in range(1,m+1))/m))
    counts={}
    records=[]
    counts['complete_homogeneous_partition_polynomials']=0
    for m in range(1,maximum+1):
        independent=sp.S.Zero
        for partition in integer_partitions(m):
            term=sp.S.One
            for r in set(partition):
                k=partition.count(r)
                term *= H[r-1]**k/sp.Integer(r)**k/sp.factorial(k)
            independent += term
        assert sp.expand(independent-h[m]) == 0
        counts['complete_homogeneous_partition_polynomials'] += 1
    counts['positive_integer_gamma_ratio_specializations']=0
    for n in range(9):
        denominator=sp.Poly(sp.prod(1-t/j for j in range(1,n+1)),t)
        series=[sp.S.One]
        for m in range(1,maximum+1):
            series.append(-sum(denominator.nth(j)*series[m-j] for j in range(1,min(m,n)+1)))
        substitutions={H[r-1]:sum(sp.Rational(1,j)**r for j in range(1,n+1))
                       for r in range(1,maximum+1)}
        for m in range(1,maximum+1):
            assert h[m].subs(substitutions) == series[m]
            counts['positive_integer_gamma_ratio_specializations'] += 1
    counts['negative_integer_residues']=0
    counts['first_pole_residues']=0
    for n in range(9):
        # Gamma(1+t)/Gamma(t-n) is a polynomial; Gamma(x)'s residue
        # at x=-n is (-1)^n/n!. This route does not use h_m.
        residue=sp.expand(sp.Rational((-1)**n,factorial(n))*sp.prod(t-r for r in range(n+1)))
        for m in range(1,maximum+1):
            computed=(-1)**m*factorial(m)*residue.coeff(t,m)
            expected=-factorial(m)*elementary(n,m-1)
            assert computed == expected
            counts['negative_integer_residues'] += 1
            if n == m-1:
                assert computed == -m
                counts['first_pole_residues'] += 1
    counts['regular_negative_integer_values']=0
    for m in range(2,maximum+1):
        # a(t)=d/dx [Gamma(1+t) Gamma(1+x)/Gamma(1+t+x)]_{x=0}.
        a=sum((-1)**r*Z[r+1]*t**r for r in range(1,m))
        for j in range(m-1):
            # Constant and first x coefficient of prod_{r=1}^j(1+t/(x-r)).
            A0=sp.prod(1-t/r for r in range(1,j+1))
            A1=sum(-t/sp.Integer(r)**2*sp.prod(1-t/k for k in range(1,j+1) if k!=r)
                   for r in range(1,j+1))
            regular_constant=sp.expand(A0+t*A1+t*A0*a)
            computed=sp.expand((-1)**m*factorial(m)*regular_constant.coeff(t,m))
            expected=-factorial(m)*sum(elementary(j,k)*Z[m-k] for k in range(j+1))
            assert sp.expand(computed-expected) == 0
            counts['regular_negative_integer_values'] += 1
            records.append({'m':m,'j':j,'value':str(expected)})
    counts['origin_and_unit_values']=0
    for m in range(2,maximum+1):
        assert h[m].subs(dict.fromkeys(H,0)) == 0
        a=sum((-1)**r*Z[r+1]*t**r for r in range(1,m))
        assert sp.expand((-1)**m*factorial(m)*(1+t*a).expand().coeff(t,m)) == -factorial(m)*Z[m]
        counts['origin_and_unit_values'] += 2
    return {'maximum_order':maximum,'residue_pole_indices':list(range(9)),
            'assertions':sum(counts.values()),'categories':counts,
            'regular_endpoint_formulas':records}


def gamma_coefficient_taylor(max_m, order):
    """Coefficients C_m(x), using a bivariate analytic Gamma ratio.

    F(t,x)=Gamma(1+t)Gamma(1+x)/Gamma(1+t+x),
    G(t,x)=(1+t/x) F(t,x). No negative powers are evaluated.
    """
    size=order+2
    logarithm=[[mp.mpf(0)]*size for _ in range(max_m+1)]
    for a in range(1,max_m+1):
        for b in range(1,size):
            rational=mp.mpf(factorial(a+b-1))/(factorial(a)*factorial(b))
            logarithm[a][b]=(-1)**(a+b+1)*rational*mp.zeta(a+b)
    f=[[mp.mpf(0)]*size for _ in range(max_m+1)]
    f[0][0]=mp.mpf(1)
    for a in range(1,max_m+1):
        for j in range(1,size):
            value=mp.mpf(0)
            for r in range(1,a+1):
                value += r*sum(logarithm[r][k]*f[a-r][j-k] for k in range(1,j+1))
            f[a][j]=value/a
    result={}
    for m in range(2,max_m+1):
        result[m]=[(-1)**m*factorial(m)*(f[m][j]+f[m-1][j+1]) for j in range(order+1)]
    return result


def normalizers_at(x,max_m):
    H=[mp.mpf(0),mp.digamma(x)+mp.euler]
    H.extend(mp.zeta(r)-mp.zeta(r,x) for r in range(2,max_m+1))
    h=[mp.mpf(1)]
    for m in range(1,max_m+1):
        h.append(sum(H[r]*h[m-r] for r in range(1,m+1))/m)
    return [factorial(m)*h[m] for m in range(max_m+1)]


def inverse_gamma_coefficients(max_m):
    a=[mp.mpf(0),mp.euler]
    a.extend(-(-1)**r*mp.zeta(r)/r for r in range(2,max_m+1))
    c=[mp.mpf(1)]
    for m in range(1,max_m+1):
        c.append(sum(r*a[r]*c[m-r] for r in range(1,m+1))/m)
    return c


def completed_kernel(d, cutoff=160):
    # t=exp(-u) removes both the endpoint subtraction and dt/t.
    # delta(t)=-log((1-exp(-t))/t) is evaluated by its analytic
    # Bernoulli series when t is small. The binomial difference avoids
    # subtraction of nearly equal logarithmic powers.
    bernoulli=[mp.bernoulli(2*k)/(2*k*factorial(2*k)) for k in range(1,25)]
    def delta(t):
        if t < mp.mpf('0.05'):
            return t/2-sum(bernoulli[k-1]*t**(2*k) for k in range(1,25))
        return -mp.log(-mp.expm1(-t)/t)
    def small(u):
        t=mp.exp(-u);v=delta(t)
        return sum(comb(d,k)*u**(d-k)*v**k for k in range(1,d+1))
    def large(t):
        return (-mp.log1p(-mp.exp(-t)))**d/t
    low=mp.quad(small,[0,1,3,8,20,50,cutoff])
    high=mp.quad(large,[1,2,5,15,40,cutoff])
    # Explicit analytic bounds on the two discarded tails, before rounding.
    # 0 <= delta(exp(-u)) <= exp(-u)/2 for u>=0.
    low_tail=mp.mpf(d)/2*mp.exp(-cutoff)*sum(
        comb(d-1,k)*mp.mpf('0.5')**(d-1-k)*factorial(k)*sum(mp.mpf(cutoff)**j/factorial(j) for j in range(k+1))
        for k in range(d))
    high_tail=mp.mpf(2)**d*mp.exp(-d*cutoff)/(d*cutoff)
    return low+high,low_tail+high_tail


def numerical_checks(dps=70):
    mp.mp.dps=dps
    maximum=7
    local_order=64
    local=gamma_coefficient_taylor(maximum,local_order)
    c=inverse_gamma_coefficients(maximum)
    switch=mp.mpf(1)/8
    result=[]
    checks=[]
    for m in range(2,maximum+1):
        # The short endpoint segment is integrated as an analytic power
        # series, not by cancellation-prone quadrature of polygammas.
        local_integral=sum(local[m][j]*switch**(j+1)/(j+1) for j in range(local_order+1))
        ordinary=mp.quadgl(lambda x:normalizers_at(x,m)[m],[switch,mp.mpf('0.25'),mp.mpf('0.5'),1])
        lhs=local_integral+ordinary
        kernel,bound=completed_kernel(m-1)
        lam=c[m]+kernel/factorial(m-1)
        rhs=factorial(m)*(c[m]-lam)
        error=abs(lhs-rhs)
        assert error < mp.mpf('1e-45')
        # A genuinely independent local formula at a regular point.
        local_value=mp.polyval(list(reversed(local[m])),switch)
        direct_value=normalizers_at(switch,m)[m]
        assert abs(local_value-direct_value) < mp.mpf('1e-45')
        # Repeating only the local cutoff answers its concrete truncation risk.
        switch2=mp.mpf(1)/16
        lhs2=sum(local[m][j]*switch2**(j+1)/(j+1) for j in range(local_order+1))
        lhs2 += mp.quadgl(lambda x:normalizers_at(x,m)[m],[switch2,switch,mp.mpf('0.25'),mp.mpf('0.5'),1])
        assert abs(lhs-lhs2) < mp.mpf('1e-45')
        result.append({'m':m,'ordinary_gamma_coefficient_integral':mp.nstr(lhs,58),
                       'completed_kernel_integral':mp.nstr(kernel,58),
                       'inverse_gamma_coefficient_c_m':mp.nstr(c[m],58),
                       'lambda_m_minus_1':mp.nstr(lam,58),
                       'm_factorial_c_minus_lambda':mp.nstr(rhs,58),
                       'absolute_residual':mp.nstr(error,8),
                       'cutoff_change_residual':mp.nstr(abs(lhs-lhs2),8),
                       'local_value_residual':mp.nstr(abs(local_value-direct_value),8),
                       'analytic_kernel_tail_bound_before_rounding':mp.nstr(bound,8)})
        print('Verified ordinary Gamma-normalizer integral m='+str(m)+', residual '+mp.nstr(error,8),flush=True)
        if m==2:
            expected=-mp.stieltjes(1)
            assert abs(lam-expected) < mp.mpf('1e-45')
            checks.append({'identity':'lambda_1=-ordinary_Stieltjes_gamma_1',
                           'absolute_residual':mp.nstr(abs(lam-expected),8)})
    return {'working_decimal_digits':dps,'local_taylor_order':local_order,
            'local_switch_points':['1/8','1/16'],'kernel_cutoff':160,
            'interval_certificate':False,'acceptance_tolerance':'1e-45',
            'comparisons':result,'additional_checks':checks,
            'note':'Kernel tail bounds exclude quadrature, Taylor truncation, and rounding error; equality remains an analytic theorem.'}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--dps',type=int,default=70)
    parser.add_argument('--exact-only',action='store_true')
    parser.add_argument('--output',type=Path,default=Path(__file__).resolve().parent.parent / 'results' / 'gamma_verification.json')
    args=parser.parse_args()
    result={'exact':exact_checks(),'versions':{'sympy':sp.__version__,'mpmath':mp.__version__}}
    print('Passed '+str(result['exact']['assertions'])+' exact checks.',flush=True)
    if not args.exact_only:
        result['numeric']=numerical_checks(args.dps)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'output':str(args.output),'exact_assertions':result['exact']['assertions'],
                      'numeric':result.get('numeric',{}).get('comparisons',[])},indent=2),flush=True)


if __name__=='__main__':
    main()
