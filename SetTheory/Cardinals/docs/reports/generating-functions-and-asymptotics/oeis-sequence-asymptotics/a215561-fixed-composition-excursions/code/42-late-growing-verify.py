#!/usr/bin/env python3
"""Reproducible checks for balanced late-growing permutations.

Exact DP and algebraic checks are certificates for the stated finite computations,
not substitutes for the proofs in the article. Numerical root values and ratios
are diagnostics only. Run from any directory: python code/verify.py [--quick].
Requires Python >= 3.10, sympy, and mpmath. No network access is used.
"""
from __future__ import annotations
import argparse
import csv
from fractions import Fraction
from itertools import product
from math import factorial
from pathlib import Path
import time
import mpmath as mp
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'data'

def steps(r: int) -> tuple[int, ...]:
    if r < 2:
        raise ValueError('r must be at least 2')
    return tuple(2*i-r-1 for i in range(1, r+1)) if r % 2 == 0 else tuple(i-(r+1)//2 for i in range(1, r+1))

def balanced_dp(r: int, bound: int) -> list[tuple[int, int, int, int]]:
    """Return (n, excursions, primitive excursions, total return count).

    States are compositions 0 <= k_i <= bound. Ordinary lexicographic order is
    topological, since each predecessor reduces a coordinate. A return is a
    nonempty prefix of height zero, including the endpoint.
    """
    base = bound+1
    jumps = steps(r)
    strides = [base**(r-1-i) for i in range(r)]
    size = base**r
    e = [0]*size
    g = [0]*size  # positive-height paths with no prior nonempty return
    moments = [0]*size
    e[0] = g[0] = 1
    rows = [(0, 1, 0, 0)]
    for idx, k in enumerate(product(range(base), repeat=r)):
        if idx == 0:
            continue
        height = sum(a*b for a, b in zip(k, jumps))
        if height < 0:
            continue
        preds = [idx-stride for ki, stride in zip(k, strides) if ki]
        total = sum(e[j] for j in preds)
        strict = sum(g[j] for j in preds)
        moment = sum(moments[j] for j in preds)
        e[idx] = total
        if height == 0:
            moments[idx] = moment+total
        else:
            moments[idx] = moment
            g[idx] = strict
        if all(ki == k[0] for ki in k):
            rows.append((k[0], total, strict, moments[idx]))
    return rows

def critical_constant(r: int) -> tuple[mp.mpf, str]:
    """Algebraic root prescription evaluated to 60 digits (not interval-certified)."""
    u = sp.Symbol('u')
    a = -min(steps(r))
    q = sp.Poly(sum(u**(a+s) for s in steps(r))-r*u**a, u)
    reduced, rem = sp.div(q, sp.Poly((u-1)**2, u))
    assert rem.is_zero
    roots = sp.nroots(reduced, n=70, maxsteps=1000) if reduced.degree() else []
    small = [z for z in roots if abs(complex(z)) < 1-1e-12]
    assert len(small) == a-1
    val = mp.mpc((-1)**(a+1)*r)
    for z in small:
        val *= mp.mpc(str(sp.re(z)), str(sp.im(z)))
    assert abs(val.imag) < mp.mpf('1e-55')
    assert val.real > 1
    return val.real, str(reduced.as_expr())

def polynomial_check() -> None:
    """Verify the sextic elimination identity exactly with rational functions."""
    a,b,c,d,e,y,z = sp.symbols('a b c d e y z')
    A, B, C = a*e, b*d, a*d*d+b*b*e
    F = -A**3*y**6 + A**2*(1-c)*y**5 + (A**2-A*B)*y**4 + (2*A*(c-1)-C)*y**3 + (A-B)*y**2 + (1-c)*y-1
    U, Z = -a*y, -1/(e*y)
    V = y*(a*d*y+b)/(1-a*e*y*y)
    W = -d/e-V
    factor = sp.expand(e*(z*z-V*z+U)*(z*z-W*z+Z))
    kernel = e*z**4+d*z**3+(c-1)*z**2+b*z+a
    diff = sp.Poly(factor-kernel, z)
    assert all(sp.cancel(diff.nth(j)) == 0 for j in (0,1,3,4))
    ratio = sp.factor(diff.nth(2)/F)
    assert ratio == 1/(y*(a*e*y**2-1)**2)
    assert sp.expand(F.subs({a:0,b:0,c:0,d:0,e:0})) == y-1


def bridge_exp_check(r: int, bound: int) -> int:
    """Check E=exp(B) coefficientwise in a small rectangular truncation.

    Euler's identity: |k| E_k = sum_{0<ell<=k, s.ell=0}
    multinomial(|ell|;ell) E_{k-ell}.
    This is independent of the path-recursion computation used for E_k.
    """
    jumps = steps(r)
    zero = (0,)*r
    counts = {zero: 1}
    checks = 0
    bridges: dict[tuple[int,...], int] = {}
    for k in product(range(bound+1), repeat=r):
        if k == zero:
            continue
        h = sum(x*y for x,y in zip(k,jumps))
        if h < 0:
            counts[k] = 0
            continue
        value = 0
        for i,ki in enumerate(k):
            if ki:
                pred = list(k); pred[i]-=1
                value += counts[tuple(pred)]
        counts[k] = value
        if h == 0:
            # Compute with a single division to make divisibility explicit.
            denom = 1
            for ki in k:
                denom *= factorial(ki)
            mult = factorial(sum(k))//denom
            bridges[k] = mult
    for k,value in counts.items():
        if k == zero or sum(x*y for x,y in zip(k,jumps)) != 0:
            continue
        rhs = sum(mult*counts[tuple(ki-li for ki,li in zip(k,ell))]
                  for ell,mult in bridges.items() if all(li<=ki for li,ki in zip(ell,k)))
        assert sum(k)*value == rhs, (r,k,value,rhs)
        checks += 1
    return checks


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--quick', action='store_true', help='smaller exact DP boxes')
    args = parser.parse_args()
    OUT.mkdir(exist_ok=True)
    mp.mp.dps = 65
    log = []
    def record(s: str) -> None:
        print(s, flush=True); log.append(s)
    record('Late-growing permutations: reproducible verification run')
    record('Arithmetic assertions are exact; decimal asymptotics are diagnostics.')
    polynomial_check()
    record('PASS: exact sextic elimination and branch at the origin')
    for r,b in [(2,5),(3,4),(4,3),(5,2)]:
        count = bridge_exp_check(r,b)
        record(f'PASS: bridge-exponential identity, r={r}, bound={b}, {count} nonempty bridge coefficients')
    constants = {}
    with (OUT/'constants.csv').open('w', newline='') as f:
        writer = csv.writer(f)
        writer.writerow(['r','E_r','c_r_OEIS_normalization','lim_primitive_probability','lim_mean_returns','deflated_kernel'])
        for r in range(2,13):
            E,q = critical_constant(r); constants[r] = E
            c = E/(mp.sqrt(r)*mp.power(2,mp.mpf(r-1)/2))
            writer.writerow([r,mp.nstr(E,55),mp.nstr(c,55),mp.nstr(1/E**2,40),mp.nstr(2*E-1,40),q])
            record(f'r={r}: E={mp.nstr(E,24)}, c={mp.nstr(c,24)}')
    phi = (1+mp.sqrt(5))/2
    assert mp.almosteq(constants[2],2)
    assert mp.almosteq(constants[3],3)
    assert abs(constants[4]-4*(phi-mp.sqrt(phi))) < mp.mpf('1e-55')
    assert abs(constants[5]-5*(3-mp.sqrt(5))/2) < mp.mpf('1e-55')
    record('PASS: numerical root prescription agrees with four exact radical constants')
    expected = {
        4: [1,7,403,40350,5223915,783353872,129141898872],
        5: [1,35,18720,19369350,27032968200,44776592395920,82881380383401600],
    }
    bounds = {4:8,5:6,6:4,7:3} if args.quick else {4:30,5:15,6:9,7:5}
    with (OUT/'exact_counts.csv').open('w', newline='') as f, (OUT/'asymptotic_diagnostics.csv').open('w',newline='') as g:
        wc,wg = csv.writer(f),csv.writer(g)
        wc.writerow(['r','n','T_r_n','primitive_count','sum_of_return_counts'])
        wg.writerow(['r','n','ratio_to_E_multinomial_over_rn','primitive_probability','mean_returns'])
        for r,bound in bounds.items():
            start=time.perf_counter()
            rows=balanced_dp(r,bound)
            for n,e,i,m in rows:
                wc.writerow([r,n,e,i,m])
                if n:
                    mult = factorial(r*n)//factorial(n)**r
                    leading = constants[r]*mp.mpf(mult)/(r*n)
                    wg.writerow([r,n,mp.nstr(mp.mpf(e)/leading,20),mp.nstr(mp.mpf(i)/e,20),mp.nstr(mp.mpf(m)/e,20)])
                if r in expected and n < len(expected[r]):
                    assert e == expected[r][n], (r,n,e)
            n,e,i,m=rows[-1]
            record(f'PASS: exact DP r={r}, n=0..{bound}; last ratio={mp.nstr(mp.mpf(e)/(constants[r]*mp.mpf(factorial(r*n)//factorial(n)**r)/(r*n)),15)}, primitive={mp.nstr(mp.mpf(i)/e,12)}, mean={mp.nstr(mp.mpf(m)/e,12)}; {time.perf_counter()-start:.2f}s')
    record('All assertions passed. No recurrence conjecture is used by the computations.')
    (OUT/'verification.txt').write_text('\n'.join(log)+'\n')

if __name__ == '__main__':
    main()
