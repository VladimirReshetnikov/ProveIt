#!/usr/bin/env python3
"""Reproduce exact-arithmetic tests and numerical tables in article.tex."""
from __future__ import annotations
import argparse
import csv
import json
import platform
import sys
from fractions import Fraction
from math import factorial
from pathlib import Path
import mpmath as mp
from catalan_partitions import (
    catalan, constants, core_mu, exact_coefficients,
    explicit_log_approximation, fourier_data, inverse_log_approximation,
    log_product_and_scaled_cumulants, phase, phase_lattice, r, saddle,
)


def gaussian_coefficients(j: int):
    """Multi-indices and exact rational weights for saddle correction E_j."""
    if j < 0:
        raise ValueError('j must be nonnegative')
    result = []
    def visit(rr, budget, exponents):
        if rr > 2*j+2:
            if budget:
                return
            R = sum(k*r0 for r0, k in exponents.items())
            moment = 1
            for i in range(1, R, 2):
                moment *= i
            den = 1
            for r0, k in exponents.items():
                den *= factorial(k)*factorial(r0)**k
            result.append((dict(exponents), Fraction((-1)**(R//2)*moment, den)))
            return
        for k in range(budget//(rr-2)+1):
            if k:
                exponents[rr] = k
            else:
                exponents.pop(rr, None)
            visit(rr+1, budget-(rr-2)*k, exponents)
        exponents.pop(rr, None)
    visit(3, 2*j, {})
    return result


def restricted_snapshots(nmax: int):
    p = [0]*(nmax+1)
    p[0] = 1
    snapshots = {}
    k, c = 1, 1
    while c <= nmax:
        for n in range(c, nmax+1):
            p[n] += p[n-c]
        snapshots[k] = p[nmax]
        c = c*2*(2*k+1)//(k+2)
        k += 1
    return p, snapshots


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--max-n', type=int, default=1_000_000)
    ap.add_argument('--dps', type=int, default=60)
    ap.add_argument('--output', type=Path, default=Path(__file__).resolve().parents[1]/'data')
    args = ap.parse_args()
    if args.max_n < 1000 or args.dps < 30:
        ap.error('use --max-n >= 1000 and --dps >= 30')
    mp.mp.dps = args.dps
    args.output.mkdir(parents=True, exist_ok=True)
    p, snapshots = restricted_snapshots(args.max_n)
    checks = []
    expected = [1,1,2,2,3,4,5,6,7,8,10,11,13,14,17,19,22,24,27,30]
    assert p[:20] == expected
    checks.append('20 OEIS initial terms agree exactly; unit part is not duplicated')

    # Independent logarithmic-derivative recurrence n*p[n] = sum b[j]*p[n-j].
    cap = 300
    b = [0]*(cap+1)
    k=1
    while catalan(k) <= cap:
        c=catalan(k)
        for j in range(c, cap+1, c):
            b[j] += c
        k += 1
    q=[1]
    for n in range(1, cap+1):
        num=sum(b[j]*q[n-j] for j in range(1, n+1))
        assert num % n == 0
        q.append(num//n)
    assert q == p[:cap+1]
    checks.append('independent coefficient recurrence agrees for n=0..300')

    alpha,A,eta,C=constants()
    for M in range(0,21):
        direct=sum(mp.log(catalan(k)) for k in range(1,M+1))
        barnes=(alpha*M*(M+1)/2-M*mp.log(mp.pi)/2
                +mp.log(mp.barnesg(M+mp.mpf('1.5')))
                -mp.log(mp.barnesg(M+3))-mp.log(mp.barnesg(mp.mpf('1.5'))))
        assert abs(direct-barnes) < mp.mpf(10)**(-args.dps+8)
    checks.append('Barnes G product identity checked at M=0..20')

    phase_errors=[]
    for th in [mp.mpf(k)/10 for k in range(10)]:
        f=phase(th); l=phase_lattice(th)
        err=max(abs(f[0]-l[0]),abs(f[3]-l[1]))
        phase_errors.append(err)
        assert err < mp.mpf(10)**(-args.dps+8)
    checks.append('Fourier and real-lattice phase formulas agree at 10 phases')

    expected_leading=[Fraction(-1,12),Fraction(1,288),Fraction(139,51840)]
    edgeworth={}
    for j in range(1,5):
        terms=gaussian_coefficients(j)
        lead=sum((w*__import__('functools').reduce(lambda x, item:x*factorial(item[0]-1)**item[1], exps.items(), 1)
                  for exps,w in terms),Fraction(0))
        if j<=3:
            assert lead==expected_leading[j-1]
        edgeworth[str(j)]={'terms':[{'exponents':e,'coefficient':str(w)} for e,w in terms],
                           'universal_leading_coefficient':str(lead)}
    checks.append('Gaussian multi-index algebra checked through the first 3 universal coefficients')

    samples=[n for n in [100,1000,10000,100000,1000000] if n<=args.max_n]
    rows=[]
    inverse=[]
    for n in samples:
        sp=saddle(n)
        lp=mp.log(p[n])
        row={'n':n,'p_exact':str(p[n]),'m':mp.nstr(sp.m,25),'log10_p':mp.nstr(lp/mp.log(10),25)}
        for j in range(3):
            row[f'saddle_{j}_relative_error']=mp.nstr(mp.expm1(sp.log_approximation(j)-lp),18)
        for j in range(2):
            row[f'explicit_{j}_relative_error']=mp.nstr(mp.expm1(explicit_log_approximation(n,j)-lp),18)
        rows.append(row)
        inverse.append({'n':n,'log_y':mp.nstr(lp,25),
            'leading_relative_error':mp.nstr(mp.expm1(inverse_log_approximation(lp,0)-mp.log(n)),18),
            'corrected_relative_error':mp.nstr(mp.expm1(inverse_log_approximation(lp,1)-mp.log(n)),18)})

    # Check the phase-resolved H expansion directly, without coefficient asymptotics.
    K=-mp.mpf(3)/4*mp.log(2*mp.pi)-mp.log(mp.barnesg(mp.mpf('1.5')))
    hrows=[]
    for mm in ['10.2','30.2','100.2','300.2']:
        m=mp.mpf(mm)
        H,_=log_product_and_scaled_cumulants(r(m),1)
        psi,_,_,pa=phase(m)
        H0=alpha*m*m/2-(mp.mpf('1.5')+alpha/2)*m+mp.mpf(15)/8*mp.log(m)-mp.mpf(9)/8-K+psi
        H1=H0+(mp.mpf(27)/16-mp.mpf('1.5')*pa)/m
        hrows.append({'m':mm,'m_squared_residual':mp.nstr((H-H1)*m*m,22)})

    sp=saddle(args.max_n)
    M=int(mp.floor(sp.m)); theta=sp.m-M
    largest=[]
    for offset in [-2,-1,0,1]:
        cutoff=M+offset
        exact=mp.mpf(snapshots.get(cutoff,p[args.max_n]))/p[args.max_n]
        cdf=mp.mpf(1)
        for j in range(offset+1,offset+14):
            cdf *= -mp.expm1(-mp.power(4,mp.mpf(j)-theta))
        largest.append({'n':args.max_n,'offset':offset,'cutoff_index':cutoff,
            'exact_cdf':mp.nstr(exact,22),'limit_cdf':mp.nstr(cdf,22),
            'difference':mp.nstr(exact-cdf,15)})

    kappa,coeffs,_=fourier_data(args.dps,12)
    result={'python':sys.version,'platform':platform.platform(),'mpmath':mp.__version__,
        'dps':args.dps,'max_n':args.max_n,'checks':checks,
        'max_phase_crosscheck_error':mp.nstr(max(phase_errors),12),
        'constants':{'alpha':mp.nstr(alpha,35),'A':mp.nstr(A,35),'eta':str(eta),'C':mp.nstr(C,35),
                     'phase_mean':mp.nstr(alpha/12+kappa/alpha,35),
                     'first_harmonic_amplitude':mp.nstr(2*abs(coeffs[0]),35)},
        'coefficient_tables':rows,'inverse_tables':inverse,'H_expansion':hrows,
        'largest_index':largest,'gaussian_coefficients':edgeworth,
        'status':'Exact integer checks and high-precision floating-point diagnostics; not interval certification.'}
    (args.output/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
    for name, data in [('coefficient_errors',rows),('inverse_errors',inverse),('largest_index',largest)]:
        with (args.output/(name+'.csv')).open('w',newline='') as f:
            w=csv.DictWriter(f,fieldnames=data[0].keys());w.writeheader();w.writerows(data)
    # Include the independently checked small b-file only (generated, not downloaded).
    with (args.output/'a033552_0_300.txt').open('w') as f:
        f.write('# Independently generated by the accompanying exact-integer program.\n')
        for n in range(301):f.write(f'{n} {p[n]}\n')
    print(json.dumps({k:result[k] for k in ['checks','max_phase_crosscheck_error','constants',
                    'coefficient_tables','inverse_tables','H_expansion','largest_index']},indent=2))

if __name__=='__main__':
    main()
