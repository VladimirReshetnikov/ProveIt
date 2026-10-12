#!/usr/bin/env python3
"""54 non-certified floating-point diagnostics; requires mpmath.
These supplement, but do not replace, the exact algebra and written proofs.
"""
from __future__ import annotations
from collections import Counter
from fractions import Fraction
from math import comb, factorial
from pathlib import Path
import json, platform, time
import mpmath as mp
from verify_exact import beta_integral, next_bell

mp.mp.dps = 80
OUT = Path(__file__).resolve().parents[1]/'results'
OUT.mkdir(exist_ok=True)
checks = []

def number(q):
    if isinstance(q, Fraction): return mp.mpf(q.numerator)/q.denominator
    return mp.mpf(q)

def check(label, a, b):
    error = abs(a-b)/max(mp.mpf(1), abs(a), abs(b))
    checks.append({'name': label, 'relative_or_absolute_residual': mp.nstr(error,12),
                   'pass': bool(error < mp.mpf('1e-55'))})

def rb(b, k):
    return sum(mp.mpf(comb(b-2,j)*3**j)/((k+2*j+1)*(k+2*j+3)*(k+2*j+5))
               for j in range(b-1))/(factorial(b)*mp.mpf(24)**(b-1))

def gamma_coordinate(a, degree):
    return mp.diff(lambda y: mp.gamma(a)*mp.gamma(1-y)/mp.gamma(a-y),0,degree)/factorial(degree)

start = time.perf_counter()
# 24 beta kernels: rational polynomial evaluation versus analytic quadrature.
for d in range(1,7):
    for extra in range(4):
        counts = {0:1,d:2+extra}
        if d >= 2: counts[1] = 2
        mon = tuple(sorted(j for j, multiplicity in counts.items() for _ in range(multiplicity)))
        def integrand(v):
            result = v**d*(1-v)**d
            for j, multiplicity in counts.items():
                exponent = multiplicity-(2 if j==d else 0)
                result *= (v**(j+1)+(-1)**j*(1-v)**(j+1))**exponent
            return result
        check(f'beta_d{d}_multiplicity{2+extra}', number(beta_integral(mon)), mp.quad(integrand,[0,mp.mpf('.5'),1]))
# 10 reciprocal-Gamma differential identities, independent of quadrature.
bell = {():Fraction(1)}
for order in range(12):
    if order>=2:
        x = mp.mpf(13)/10+mp.mpf(order)/31
        derivative_values = {j:mp.polygamma(j,x) for j in range(order)}
        value = sum(number(c)*mp.fprod(derivative_values[j] for j in mon) for mon,c in bell.items())
        independent = (-1)**order*mp.gamma(x)*mp.diff(lambda q:1/mp.gamma(q),x,order)
        check(f'gamma_derivative_m{order}', value, independent)
    bell = next_bell(bell)
# 12 harmonic values in distinct beta and Gamma coordinates.
for b in range(2,6):
    for r in range(3):
        beta = 3*(-1)**r*sum(comb(b-2,j)*3**j*mp.diff(lambda q:mp.beta(mp.mpf(j)+mp.mpf('.5'),q),2,r)
                 for j in range(b-1))/(2*factorial(b)*mp.mpf(24)**b*factorial(r))
        gamma = sum(comb(b-2,j)*3**j*(-gamma_coordinate(mp.mpf(j)+mp.mpf('.5'),r+1)
                    +2*gamma_coordinate(mp.mpf(j)+mp.mpf('1.5'),r+1)
                    -gamma_coordinate(mp.mpf(j)+mp.mpf('2.5'),r+1))
                    for j in range(b-1))/(16*factorial(b)*mp.mpf(24)**(b-1))
        check(f'harmonic_b{b}_r{r}', beta, gamma)
# 8 geometrically convergent series versus polylogarithmic quadrature.
for b in range(2,6):
    for m in (1,2):
        z = mp.mpf('.3') if m==1 else mp.mpf('.7')
        terms=[]
        for n in range(1,3000):
            term=rb(b,2*n)*z**n/n**m;terms.append(term)
            if abs(term)<mp.mpf('1e-76'):break
        else:raise RuntimeError('Series termination threshold not reached')
        direct = mp.fsum(terms)
        integral = 3*mp.quad(lambda v:(1-v*v)**2*(1+3*v*v)**(b-2)*mp.polylog(m,z*v*v),[0,1])/(factorial(b)*mp.mpf(24)**b)
        check(f'polylog_b{b}_m{m}_z{z}', direct, integral)
assert len(checks)==54
report = {'status':'PASS' if all(c['pass'] for c in checks) else 'FAIL',
          'diagnostic_count':len(checks), 'decimal_precision':mp.mp.dps,
          'tolerance':'1e-55 relative to max(1, |a|, |b|)',
          'certified_enclosures':False,'python':platform.python_version(),
          'mpmath':mp.__version__,'seconds':time.perf_counter()-start,'checks':checks}
(OUT/'numeric_report.json').write_text(json.dumps(report,indent=2))
print(json.dumps(report,indent=2))
if report['status']!='PASS':raise AssertionError('Floating-point diagnostic failure; inspect the report')
