#!/usr/bin/env python3
"""Finite exact checks and explicitly non-certified asymptotic diagnostics.

Default exact checks use only Python's standard library.  --diagnostics also
requires NumPy; --mp-check additionally requires mpmath. No network access.
"""
from __future__ import annotations
import argparse
import csv
import itertools
import json
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

def inverse_coefficients(f: list[int]) -> list[int]:
    """Lagrange inversion, using an independently derivable power recurrence."""
    if len(f) < 2 or f[0] != 0 or f[1] != 1:
        raise ValueError('Expected a tangent-to-identity integer series.')
    N = len(f) - 1
    g = [0, 1] + [0] * (N - 1)
    for n in range(2, N + 1):
        b = [1] + [0] * (n - 1)
        for m in range(1, n):
            numerator = -sum((m + (n - 1)*j)*f[j+1]*b[m-j]
                             for j in range(1, m+1))
            assert numerator % m == 0
            b[m] = numerator // m
        assert b[n-1] % n == 0
        g[n] = b[n-1] // n
    return g

def multiply(a: list[int], b: list[int], N: int) -> list[int]:
    c = [0]*(N+1)
    for i in range(min(len(a),N+1)):
        if a[i]:
            for j in range(min(len(b),N+1-i)):
                c[i+j] += a[i]*b[j]
    return c

def compose(f: list[int], g: list[int]) -> list[int]:
    N = min(len(f),len(g))-1
    result, power = [0]*(N+1), [1]+[0]*N
    for k in range(N+1):
        if f[k]:
            result = [x+f[k]*y for x,y in zip(result,power)]
        power = multiply(power,g,N)
    return result

def weights(N: int, s: int, nu: int) -> list[int]:
    w = [1]*(N+1)
    for j in range(1,N+1):
        w[j] = (math.factorial(j+nu)//math.factorial(1+nu))**s
    return w

def exact_checks(N: int) -> dict:
    if N < 10:
        raise ValueError('The exact order must be at least ten.')
    checks = 0
    rows = []
    identity = [0,1]+[0]*(N-1)
    for s,nu in itertools.product((1,2),(0,1)):
        w = weights(N,s,nu)
        f = [0,1]+[-w[n-1] for n in range(2,N+1)]
        g = inverse_coefficients(f)
        assert compose(f,g) == identity; checks += N+1
        assert compose(g,f) == identity; checks += N+1
        assert all(x>0 for x in g[1:]); checks += N
        rows.append({'s':s,'nu':nu,'inverse_first_12':g[1:13]})
    # Exhaustively vary all signs in a degree-ten factorial coefficient box.
    M = 10
    w = weights(M,1,0)
    extremal = [0,1]+[-w[n-1] for n in range(2,M+1)]
    majorant = inverse_coefficients(extremal)
    for signs in itertools.product((-1,1),repeat=M-1):
        f = [0,1]+[signs[n-2]*w[n-1] for n in range(2,M+1)]
        g = inverse_coefficients(f)
        for n in range(2,M+1):
            assert abs(g[n]) <= majorant[n]; checks += 1
    # Root-limit counterexample: sparse inverse, strictly positive forward.
    h = [0,1]+[-math.factorial(n-1) if n%2==0 else 0
               for n in range(2,N+1)]
    F = inverse_coefficients(h)
    assert compose(h,F) == identity; checks += N+1
    assert compose(F,h) == identity; checks += N+1
    for n in range(2,N+1):
        lower = math.factorial(n-1) if n%2==0 else (n-1)*math.factorial(n-2)
        assert F[n] >= lower; checks += 1
    # Composition/inverse algebra, with two distinct divergent coefficient scales.
    f = [0,1]+[math.factorial(n-1) for n in range(2,N+1)]
    g = [0,1]+[2**(n-1)*math.factorial(n-1) for n in range(2,N+1)]
    h = compose(f,g)
    lhs = inverse_coefficients(h)
    rhs = compose(inverse_coefficients(g),inverse_coefficients(f))
    assert lhs == rhs; checks += N+1
    return {'exact_checks_passed':True,'exact_order':N,'scalar_equalities_or_inequalities':checks,
            'sign_patterns_exhausted':2**(M-1),'sign_box_degree':M,
            'examples':rows,'sparse_inverse_degrees_0_to_12':([0,1]+[-math.factorial(n-1) if n%2==0 else 0 for n in range(2,13)]),
            'positive_forward_degrees_0_to_12':F[:13],
            'scope':'Finite algebraic checks, not asymptotic proofs or Lean verification.'}

def normalized_extremum(n: int, s: float, C: float=1.0, nu: int=0):
    """Compute R_n at A=1 in extended-range floating point, O(n^2) work."""
    import numpy as np
    T = np.longdouble
    if np.finfo(T).maxexp < 10000:
        raise RuntimeError('Diagnostics require an extended-range NumPy longdouble.')
    logs = np.zeros(n+nu+1,dtype=T)
    logs[1:] = np.cumsum(np.log(np.arange(1,n+nu+1,dtype=T)))
    logw = T(s)*(logs[np.arange(n)+nu]-logs[1+nu])
    B = np.zeros(n,dtype=T)
    B[0] = 1
    for m in range(1,n):
        j = np.arange(1,m)
        ratios = np.exp(logw[j]+logw[m-j]-logw[m])
        total = T(n*m)
        if m>1:
            total += np.sum((T(m)+T(n-1)*j)*ratios*B[m-j],dtype=T)
        B[m] = T(C)*total/T(m)
    R = B[n-1]/(T(n)*T(C))
    if not np.isfinite(R) or R <= 0:
        raise ArithmeticError('Non-finite diagnostic. Reduce n or use mpmath.')
    return R

def diagnostics(out: Path) -> list[dict]:
    import numpy as np
    rows=[]
    for nu in (0,1):
        for s in (0.25,0.5,0.75,1.0,1.25):
            for n in (40,80,160,320,640,1280):
                R=normalized_extremum(n,s,1.0,nu)
                logR=np.log(R)
                mu=np.longdouble(n)**np.longdouble(1-s)
                rows.append({'n':n,'s':s,'nu':nu,'C':1.0,
                             'log_R':format(logR,'.16g'),
                             'log_R_over_n_power':format(logR/mu,'.16g'),
                             'log_R_minus_n_power':format(logR-mu,'.16g')})
    with (out/'diagnostics.csv').open('w',newline='',encoding='utf-8') as fh:
        w=csv.DictWriter(fh,fieldnames=list(rows[0])); w.writeheader(); w.writerows(rows)
    cross=[]
    for tau in (-2.,-1.,0.,1.,2.):
        for n in (80,320,1280):
            s=1+tau/math.log(n)
            R=normalized_extremum(n,s,1.,0)
            cross.append({'n':n,'tau':tau,'s':s,
                          'R':format(R,'.16g'),
                          'predicted_limit':math.exp(math.exp(-tau))})
    with (out/'crossover.csv').open('w',newline='',encoding='utf-8') as fh:
        w=csv.DictWriter(fh,fieldnames=list(cross[0])); w.writeheader(); w.writerows(cross)
    return rows

def mp_cross_check() -> list[dict]:
    import mpmath as mp
    mp.mp.dps=80
    result=[]
    for s,nu in ((mp.mpf('0.5'),0),(mp.mpf('0.5'),1),(mp.mpf('0.75'),0)):
        n=80
        w=[mp.mpf(1)]+[(mp.factorial(j+nu)/mp.factorial(1+nu))**s
                       for j in range(1,n)]
        b=[mp.mpf(1)]+[mp.mpf(0)]*(n-1)
        for m in range(1,n):
            b[m]=mp.fsum((m+(n-1)*j)*w[j]*b[m-j] for j in range(1,m+1))/m
        R=b[n-1]/(n*w[n-1])
        fast=mp.mpf(str(normalized_extremum(n,float(s),1.,nu)))
        error=abs(fast/R-1)
        assert error < mp.mpf('1e-13')
        result.append({'n':n,'s':str(s),'nu':nu,'R_80_digits':mp.nstr(R,75),
                       'relative_difference':mp.nstr(error,8),
                       'certified':False})
    return result

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--order',type=int,default=40)
    parser.add_argument('--diagnostics',action='store_true')
    parser.add_argument('--mp-check',action='store_true')
    parser.add_argument('--out',type=Path,default=ROOT/'data'/'rerun')
    args=parser.parse_args(); args.out.mkdir(parents=True,exist_ok=True)
    report=exact_checks(args.order)
    if args.diagnostics:
        diagnostics(args.out)
        report['diagnostics']='Positive-term longdouble computations, not interval certificates.'
    if args.mp_check:
        report['high_precision_cross_checks']=mp_cross_check()
    (args.out/'verification.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(report,indent=2))

if __name__=='__main__':
    main()
