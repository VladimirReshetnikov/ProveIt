#!/usr/bin/env python3
"""Reproducible checks for Confluent Critical Transseries.

Exact algebraic assertions and floating-point diagnostics are reported separately.
No floating-point result is an interval certificate or a proof of an asymptotic limit.
Run from any directory: python code/verify.py --part all
"""
from __future__ import annotations
import argparse
import csv
import json
import math
import platform
from fractions import Fraction as Q
from pathlib import Path
from typing import Sequence
import mpmath as mp
import numpy as np
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "data"
DATA.mkdir(exist_ok=True)


def exp_series(g: Sequence[Q], degree: int) -> list[Q]:
    """exp(g), for g[0]=0, by its exact differential recurrence."""
    if g[0] != 0:
        raise ValueError("The constant coefficient must vanish.")
    out = [Q(0) for _ in range(degree + 1)]
    out[0] = Q(1)
    for k in range(1, degree + 1):
        out[k] = sum((j * g[j] * out[k-j] for j in range(1, k+1)), Q(0))/k
    return out


def fixed_point(degree: int, cutoff: int) -> list[Q]:
    """Solve U=sum_(j<=M) q^j exp(j U)/j^3 in Q[[q]]/(q^(N+1))."""
    u = [Q(0)] * (degree + 1)
    for _ in range(degree):
        new = [Q(0)] * (degree + 1)
        for j in range(1, min(cutoff, degree)+1):
            ex = exp_series([j*x for x in u], degree-j)
            for k in range(degree-j+1):
                new[j+k] += ex[k]/j**3
        u = new
    return u


def exact_audit() -> dict:
    assertions = 0
    for cutoff in (1, 2, 3, 5, 12):
        u = fixed_point(12, cutoff)
        for n in range(1, 13):
            g = [Q(0)] + [Q(n, j**3) if j <= cutoff else Q(0)
                            for j in range(1, n+1)]
            direct = exp_series(g, n)[n]/n
            assert direct == u[n]
            assertions += 1
    all_u = fixed_point(12, 12)
    for cutoff in (1, 2, 3, 5):
        u = fixed_point(12, cutoff)
        for n in range(1, 13):
            assert 0 < u[n] <= all_u[n]
            assertions += 1
            if n <= cutoff:
                assert u[n] == all_u[n]
                assertions += 1

    # Symbolic audit of the degree-two confluent chart; g0,g1,z1 are free.
    s, r, e, v, g0, g1, z1 = sp.symbols("s r e v g0 g1 z1")
    z0 = sp.Rational(3, 2) - 2*g0
    A = -g0*e - sp.Rational(3, 4)*v
    B = ((sp.Rational(3,2)*g0**2 - g0/2 - g1)*e**2
         + (sp.Rational(7,4)*g0 - sp.Rational(3,8) - g1-z1/2)*e*v
         + sp.Rational(15,32)*v**2 - r*v/12)
    V = 1+s*A+s*s*B
    # Terms not displayed here have total degree >=3 in (r,e,v).
    bracket = (1 - s*(e+v)*sp.log(V)
               + 2*(g0+s*g1*e)*s*(e+v)*sp.exp(-s*e*sp.log(V))
               + (z0+s*z1*e)*s*v + s*s*r*v/6)
    residual = sp.series(V**2*bracket-1, s, 0, 3).removeO().expand()
    for k in range(3):
        assert sp.simplify(residual.coeff(s, k)) == 0
        assertions += 1
    report = {
        "status": "PASS", "exact_assertions": assertions,
        "coefficient_degrees": "1 through 12",
        "cutoffs": [1,2,3,5,12],
        "chart_audit": "exact residual vanishes through total degree 2",
        "proof_assistant_verification": False,
        "rational_coefficients_full": [str(x) for x in all_u[1:]],
    }
    (DATA/"exact_checks.json").write_text(json.dumps(report, indent=2)+"\n")
    return report


def h(e: mp.mpf, x: mp.mpf) -> mp.mpf:
    if x <= 1:
        raise ValueError("h requires x>1")
    return mp.log(x) if e == 0 else mp.expm1(e*mp.log(x))/e


def scales(n: int | mp.mpf, e: mp.mpf) -> tuple[mp.mpf, mp.mpf, mp.mpf]:
    """Return c, extreme scale A, and the large root B^2=n*c*h_e(B)."""
    c = 1/mp.zeta(2-e)
    A = (n*c)**(1/(2-e))
    lo, hi = mp.mpf(2), mp.log(n)+10
    def eq(y: mp.mpf) -> mp.mpf:
        return 2*y-mp.log(n*c)-mp.log(h(e, mp.exp(y)))
    if eq(lo) >= 0:
        raise ValueError("n too small for the specified large-root bracket")
    while eq(hi) <= 0:
        hi *= 2
    for _ in range(240):
        mid = (lo+hi)/2
        if eq(mid) > 0: hi = mid
        else: lo = mid
    return c, A, mp.exp((lo+hi)/2)


def poisson_mass(n: int, e: mp.mpf, cutoff: int | None = None,
                 beta: mp.mpf = mp.mpf(1)) -> np.longdouble:
    """Positive Panjer recurrence. Includes the full infinite total intensity.

    Uses extended-range longdouble when available. Fails rather than silently
    underflowing on platforms where longdouble has binary64 exponent range.
    """
    alpha = 2-e
    c = 1/mp.zeta(alpha)
    total = n*beta*c*mp.zeta(1+alpha)
    if cutoff is not None:
        if cutoff < 1: raise ValueError("cutoff must be positive")
        total -= n*beta*c*mp.zeta(1+alpha, cutoff+1)
    if float(total) > -math.log(float(np.finfo(float).tiny)) and np.finfo(np.longdouble).maxexp < 4000:
        raise RuntimeError("This diagnostic requires extended-range longdouble; use the mpmath audit instead.")
    M = min(n, cutoff if cutoff is not None else n)
    j = np.arange(1, M+1, dtype=np.longdouble)
    weights = np.longdouble(str(n*beta*c))*np.exp(-np.longdouble(str(alpha))*np.log(j))
    p = np.zeros(n+1, dtype=np.longdouble)
    p[0] = np.exp(-np.longdouble(str(total)))
    if p[0] == 0: raise ArithmeticError("Initial probability underflowed.")
    for k in range(1, n+1):
        m = min(k, M)
        p[k] = np.dot(weights[:m], p[k-m:k][::-1])/k
    if not (0 < p[n] <= 1): raise ArithmeticError("Invalid probability")
    return p[n]


def poisson_mass_mp(n: int, e: mp.mpf, cutoff: int | None = None) -> mp.mpf:
    alpha = 2-e
    c = 1/mp.zeta(alpha)
    total = n*c*mp.zeta(1+alpha)
    if cutoff is not None: total -= n*c*mp.zeta(1+alpha, cutoff+1)
    M = min(n, cutoff if cutoff is not None else n)
    w = [mp.mpf(0)] + [n*c*j**(-alpha) for j in range(1, M+1)]
    p = [mp.exp(-total)] + [mp.mpf(0)]*n
    for k in range(1, n+1):
        p[k] = mp.fsum(w[j]*p[k-j] for j in range(1, min(k,M)+1))/k
    return p[n]


def coefficient_diagnostics() -> dict:
    mp.mp.dps = 75
    rows = []
    for n in (512, 2048, 8192):
        for lam in (-1, 0, 1):
            e = mp.mpf(lam)/mp.log(n)
            c, A, B = scales(n,e)
            p = poisson_mass(n,e)
            row = {"n": n, "lambda": lam, "epsilon": float(e),
                   "A": float(A), "B": float(B), "A_over_B": float(A/B),
                   "normal_mass_ratio": float(p)*float(mp.sqrt(2*mp.pi)*B)}
            for s0 in (mp.mpf('0.75'), mp.mpf(1), mp.mpf('1.5')):
                M = int(mp.floor(s0*A))
                pm = poisson_mass(n,e,M)
                tail = n*c*mp.zeta(3-e,M+1)
                ratio = np.exp(-np.longdouble(str(tail)))*pm/p
                key = str(float(s0))
                row["cutoff_"+key] = M
                row["ratio_"+key] = float(ratio)
            rows.append(row)
    with (DATA/"coefficient_diagnostics.csv").open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0])); w.writeheader(); w.writerows(rows)
    # Independent higher-precision recurrence checks.
    maxrel = mp.mpf(0)
    comparisons = 0
    for e in (mp.mpf('-0.1'),mp.mpf(0),mp.mpf('0.1')):
        for M in (None,24):
            pm = poisson_mass_mp(128,e,M)
            pe = mp.mpf(str(poisson_mass(128,e,M)))
            err = abs(pe/pm-1)
            maxrel=max(maxrel,err)
            assert err < mp.mpf('2e-14')
            comparisons += 1
    text = [r"\begin{tabular}{rrrrrr}", r"\toprule",
            r"$n$ & $\lambda$ & $A_n/B_n$ & $\sqrt{2\pi}B_n\Pr(S_n=n)$ & $R_n(A_n)$ & $R_n(1.5A_n)$\\",
            r"\midrule"]
    for row in rows:
        text.append(f"{row['n']} & {row['lambda']} & {row['A_over_B']:.5f} & {row['normal_mass_ratio']:.5f} & {row['ratio_1.0']:.5f} & {row['ratio_1.5']:.5f}" + " " + chr(92)*2)
    text += [r"\bottomrule",r"\end{tabular}"]
    (DATA/"coefficient_table.tex").write_text('\n'.join(text)+'\n')
    out={"status":"completed", "rows":len(rows), "independent_mp_comparisons":comparisons,
         "max_relative_disagreement":mp.nstr(maxrel,12),
         "interval_certified":False, "asymptotic_limits_not_asserted_by_tests":True}
    (DATA/"coefficient_checks.json").write_text(json.dumps(out,indent=2)+'\n')
    return out


def latex_scientific(x: float) -> str:
    """Small positive float as a typeset scientific-notation table entry."""
    mantissa, exponent = f"{x:.3e}".split("e")
    return "$" + mantissa + r"\times10^{" + str(int(exponent)) + "}$"


def inversion_diagnostics() -> dict:
    mp.mp.dps=160
    g0=mp.mpf(3)/4-mp.euler/2
    g1=mp.mpf(7)/8-3*mp.euler/4+mp.euler**2/4+mp.pi**2/24
    z1=mp.stieltjes(1)
    rows=[]
    for L in (20,40,80):
        r=mp.exp(-L)
        for tau in (-2,0,2):
            e=mp.mpf(tau)/L
            c=1/mp.zeta(2-e)
            v=1/h(e,1/r)
            delta=c*r*r*h(e,1/r)/2
            def residual(V: mp.mpf) -> mp.mpf:
                t=r*V
                F=c*(mp.polylog(3-e,mp.exp(-t))-mp.zeta(3-e)+mp.zeta(2-e)*t)
                return F/delta-1
            V=mp.findroot(residual,(mp.mpf('0.9'),mp.mpf('1.1')))
            A=-g0*e-3*v/4
            B=((mp.mpf(3)/2*g0*g0-g0/2-g1)*e*e
               +(7*g0/4-mp.mpf(3)/8-g1-z1/2)*e*v
               +15*v*v/32-r*v/12)
            err1=abs(V-(1+A))
            err2=abs(V-(1+A+B))
            assert abs(residual(V))<mp.mpf('1e-55')
            rows.append({"L":L,"tau":tau,"epsilon":float(e),"v":float(v),
                         "V":float(V),"degree1_error":float(err1),"degree2_error":float(err2)})
    with (DATA/"inversion_diagnostics.csv").open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
    text=[r"\begin{tabular}{rrrrr}",r"\toprule",
          r"$\log(1/r)$ & $\varepsilon\log(1/r)$ & $t/r$ & degree-1 error & degree-2 error\\",r"\midrule"]
    for row in rows:
        text.append(f"{row['L']} & {row['tau']} & {row['V']:.9f} & {latex_scientific(row['degree1_error'])} & {latex_scientific(row['degree2_error'])}" + " " + chr(92)*2)
    text += [r"\bottomrule",r"\end{tabular}"]
    (DATA/"inversion_table.tex").write_text('\n'.join(text)+'\n')
    out={"status":"completed","rows":len(rows),"working_decimal_digits":160,
         "root_relative_residual_threshold":"1e-55", "interval_certified":False}
    (DATA/"inversion_checks.json").write_text(json.dumps(out,indent=2)+'\n')
    return out


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--part',choices=['all','exact','coefficients','inversion'],default='all')
    args=parser.parse_args()
    report={"python":platform.python_version(),"numpy":np.__version__,
            "sympy":sp.__version__,"mpmath":mp.__version__}
    if args.part in ('all','exact'): report['exact']=exact_audit()
    if args.part in ('all','coefficients'): report['coefficients']=coefficient_diagnostics()
    if args.part in ('all','inversion'): report['inversion']=inversion_diagnostics()
    (DATA/f"run_{args.part}.json").write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__': main()
