#!/usr/bin/env python3
"""Exact and high-precision checks for the restricted-partition article.

Run: python verify.py [--quick]
Requires mpmath and sympy. Output files are written beside this script.
The checks test formulas and examples; they are not a formal proof of the
uniform asymptotic theorems.
"""
from __future__ import annotations
import argparse
import csv
import json
import math
from pathlib import Path
import time
import mpmath as mp
import sympy as sp

ROOT = Path(__file__).resolve().parent
OEIS_CUBIC = [1, 1, 5, 75, 2280, 106852, 6889527, 569704489,
57733506640, 6944433285769, 968356321790171, 153738253618009045,
27396489338187214000, 5417302365503826145732,
1177436831956414016252071, 279074576444362385794783853,
71649589941044468875380333533]

def exact_row(m: int, limit: int) -> list[int]:
    """Coefficient extraction by multiplication of geometric series."""
    if m < 0 or limit < 0:
        raise ValueError("m and limit must be nonnegative")
    a = [1] + [0] * limit
    for j in range(1, m + 1):
        for n in range(j, limit + 1):
            a[n] += a[n-j]
    return a

def independent_row(m: int, limit: int) -> list[int]:
    """Logarithmic-derivative recurrence, independent of the DP update."""
    divisor_sum = [0] * (limit + 1)
    for d in range(1, min(m, limit) + 1):
        for r in range(d, limit + 1, d):
            divisor_sum[r] += d
    p = [1] + [0] * limit
    for n in range(1, limit + 1):
        numerator = sum(divisor_sum[r] * p[n-r] for r in range(1, n+1))
        p[n], rem = divmod(numerator, n)
        assert rem == 0
    return p

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--quick', action='store_true')
    args = parser.parse_args()
    started = time.time()
    mp.mp.dps = 90
    m, c, j = sp.symbols('m c j', positive=True)
    coefficients = json.loads((ROOT / 'coefficients.json').read_text())
    if len(coefficients.get('relative', [])) < 6:
        raise ValueError('Regenerate coefficients with derive_coefficients.py --order 5 first')
    bs = [sp.sympify(v, locals={'c': c}) for v in coefficients['relative']]
    log_coeffs = [sp.sympify(v, locals={'c': c}) for v in coefficients['log']]
    relfun = [sp.lambdify(c, b, 'mpmath') for b in bs]
    logfun = [sp.lambdify(c, l, 'mpmath') for l in log_coeffs]

    checks = 0
    for r in range(1, 13):
        row = exact_row(r, 200)
        other = independent_row(r, 200)
        for actual, expected in zip(row, other):
            assert actual == expected
            checks += 1
        for N in range(1, 201):
            den = math.factorial(r) * math.factorial(r-1)
            # Clear denominators: exact rational inequalities, not floats.
            assert row[N] * den >= N**(r-1)
            A = r*(r+1)//2 - 1
            assert row[N] * den <= (N+A)**(r-1)
            if r >= 3:
                # R >= 1 + m(m-1)^2/(4N).
                assert 4*N*row[N]*den >= (4*N+r*(r-1)**2)*N**(r-1)
            checks += 3 if r >= 3 else 2

    S1 = m*(m+1)/2
    S2 = m*(m+1)*(2*m+1)/6
    beta1 = sp.expand((m-1)*S1/2)
    beta2 = sp.expand((m-1)*(m-2)*(S1**2/8-S2/24))
    D2 = sp.factor(beta2-beta1**2/2)
    assert sp.factor(beta1-m*(m*m-1)/4) == 0
    assert sp.factor(D2+m*(m*m-1)*(13*m*m+3*m-4)/288) == 0
    checks += 2

    mmax = 24 if args.quick else 60
    cmaxm = 24 if args.quick else 40
    targets: dict[int, list[tuple[str, int, int]]] = {}
    for r in range(1, mmax+1):
        targets[r] = [('cubic', r**3, 1)]
        if r <= cmaxm:
            targets[r] += [('cubic', cc*r**3, cc) for cc in range(2, 6)]
        if r <= min(20, mmax):
            targets[r].append(('quartic', r**4, 0))
        if r <= min(18, mmax):
            targets[r].append(('exponential2', 2**r, 0))
    nmax = max(n for ts in targets.values() for _, n, _ in ts)
    row = [1] + [0] * nmax
    records: list[dict[str, object]] = []
    probability: list[dict[str, object]] = []
    exacts: list[dict[str, object]] = []
    inverses: list[dict[str, object]] = []
    for r in range(1, mmax+1):
        for n in range(r, nmax+1):
            row[n] += row[n-r]
        for family, N, cc in targets[r]:
            value = row[N]
            exacts.append({'family': family, 'm':r,'N':N,'c':cc,'value':str(value)})
            if family == 'cubic':
                if cc == 1 and r < len(OEIS_CUBIC):
                    assert value == OEIS_CUBIC[r]
                    checks += 1
                leading_log = (2*r+mp.mpf(1)/(4*cc)+(r-3)*mp.log(r)
                               +(r-1)*mp.log(cc)-mp.log(2*mp.pi))
                normalized = mp.exp(mp.log(value)-leading_log)
                rec: dict[str, object] = {'m':r,'c':cc,
                    'normalized':mp.nstr(normalized,35)}
                for K in [0,1,2,3,5]:
                    approx = sum(relfun[k](cc)/mp.mpf(r)**k for k in range(K+1))
                    rec[f'rel_error_K{K}'] = mp.nstr(approx/normalized-1,25)
                records.append(rec)
                if r >= 3:
                    T = r*(r-1)//2
                    pzero = mp.mpf(row[N-T])/value
                    mean_num = sum(value-row[N-jj] for jj in range(1,r))
                    f2_num = 2*sum(value-row[N-jj]-row[N-kk]+row[N-jj-kk]
                                  for jj in range(1,r) for kk in range(jj+1,r))
                    mean = mp.mpf(mean_num)/value
                    f2 = mp.mpf(f2_num)/value
                    subset = [1] + [0]*T
                    for jj in range(1, r):
                        for tt in range(T, jj-1, -1):
                            subset[tt] += subset[tt-jj]
                    half = mp.mpf(sum(subset[tt]*row[N-tt] for tt in range(T+1)))/(2**(r-1)*value)
                    half_first = mp.exp(-mp.mpf(1)/(4*cc))*(1+(mp.mpf(1)/(2*cc)+mp.mpf(7)/(96*cc*cc))/r)
                    probability.append({'m':r,'c':cc,'P_zero':mp.nstr(pzero,25),
                        'pgf_half':mp.nstr(half,25),
                        'pgf_half_first_error':mp.nstr(half_first/half-1,25),
                        'mean':mp.nstr(mean,25),'factorial_moment_2':mp.nstr(f2,25),
                        'variance':mp.nstr(f2+mean-mean**2,25)})
                if cc == 1 and r >= 8:
                    L=mp.log(value); b=mp.mpf(2); D=mp.mpf(1)/4-mp.log(2*mp.pi)
                    w=mp.lambertw(mp.exp(b)*L); x0=L/w
                    delta0=(3*mp.log(x0)-D)/(w+1)
                    delta1=(3*delta0-delta0**2/2-logfun[0](1))/(w+1)
                    inverses.append({'family':'cubic','m':r,
                        'leading_error':mp.nstr(x0-r,25),
                        'corrected_error':mp.nstr(x0+delta0+delta1/x0-r,25)})
            elif family == 'exponential2' and r >= 8:
                b=mp.log(2); L=mp.log(value)
                F=lambda x:b*x*(x-1)-mp.loggamma(x+1)-mp.loggamma(x)
                Fprime=lambda x:b*(2*x-1)-mp.digamma(x+1)-mp.digamma(x)
                X=mp.findroot(lambda x:F(x)-L, (mp.mpf(r), mp.mpf(r)+1))
                corrected=X-X*(X*X-1)/4*mp.exp(-b*X)/Fprime(X)
                inverses.append({'family':'exponential2','m':r,
                    'leading_error':mp.nstr(X-r,25),
                    'corrected_error':mp.nstr(corrected-r,25)})
    for name,data in [('critical_errors.csv',records),('poisson_checks.csv',probability),
                      ('inverse_checks.csv',inverses)]:
        with (ROOT/name).open('w',newline='') as f:
            writer=csv.DictWriter(f,fieldnames=list(data[0]))
            writer.writeheader(); writer.writerows(data)
    (ROOT/'exact_values.json').write_text(json.dumps(exacts,indent=2)+'\n')
    report={'status':'PASS','exact_assertions':checks,'maximum_m':mmax,
            'maximum_N':nmax,'computed_samples':len(exacts),
            'decimal_precision':mp.mp.dps,'seconds':round(time.time()-started,3),
            'note':'Finite exact checks and numerical diagnostics; not formal verification.'}
    (ROOT/'verification_summary.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
    print('\nCubic c=1 relative errors:')
    for rec in records:
        if rec['c']==1 and rec['m'] in [10,20,40,60]: print(rec)
    print('\nPoisson c=1 diagnostics:')
    for rec in probability:
        if rec['c']==1 and rec['m'] in [10,20,40,60]: print(rec)
    print('\nInverse diagnostics:')
    for rec in inverses:
        if rec['m'] in [10,18,20,40,60]: print(rec)

if __name__ == '__main__':
    main()
