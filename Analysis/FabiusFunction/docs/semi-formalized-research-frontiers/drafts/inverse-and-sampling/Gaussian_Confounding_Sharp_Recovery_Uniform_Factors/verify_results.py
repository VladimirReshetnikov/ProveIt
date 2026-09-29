#!/usr/bin/env python3
"""Exact supporting checks for Gaussian Confounding and Uniform-Factor Recovery.

These finite checks do not replace the general proofs in article.tex.
Dependencies: SymPy and mpmath. Run from any working directory.
"""
from __future__ import annotations
import json
import math
import random
from fractions import Fraction
from pathlib import Path
import sympy as sp
import mpmath as mp

OUT = Path(__file__).resolve().parent / "artifacts"
OUT.mkdir(exist_ok=True)

def powers_from_elementary(e: list[sp.Expr], count: int) -> list[sp.Expr]:
    """Return p_0,...,p_count from elementary symmetric coefficients e_0=1."""
    m = len(e) - 1
    p = [sp.Integer(m)]
    for k in range(1, count + 1):
        if k <= m:
            value = sum((-1)**(i-1)*e[i]*p[k-i] for i in range(1, k))
            value += (-1)**(k-1)*k*e[k]
        else:
            value = sum((-1)**(i-1)*e[i]*p[k-i] for i in range(1, m+1))
        p.append(sp.expand(value))
    return p

def exact_shift_flow(m: int) -> dict:
    z, s = sp.symbols("z s")
    roots = [sp.Rational(i, m+1) for i in range(1, m+1)]
    base = sp.Poly(sp.prod(z-u for u in roots), z)
    e0 = [(-1)**k * base.all_coeffs()[k] for k in range(m+1)]
    e = [sum(e0[k-j]*s**j/sp.factorial(j) for j in range(k+1))
         for k in range(m+1)]
    p = powers_from_elementary(e, m+1)
    assert sp.expand(p[1] - sum(roots) - s) == 0
    for k in range(2, m+1):
        assert sp.expand(p[k] - sum(u**k for u in roots)) == 0
    assert sp.expand(sp.diff(p[m+1], s) - (-1)**(m+1)*(m+1)*e[m]) == 0
    poly = sp.Poly(sum((-1)**k*e[k]*z**(m-k) for k in range(m+1)), z)
    radius = sp.Rational(1, 4*(m+1))
    intervals = [(u-radius, u+radius) for u in roots]
    shift = sp.Rational(1, 1024)
    for _ in range(100):
        candidate = sp.Poly(poly.as_expr().subs(s, shift), z)
        if all(candidate.eval(a)*candidate.eval(b) < 0 for a,b in intervals):
            break
        shift /= 2
    else:
        raise AssertionError("No rational simple-root certificate found")
    # m disjoint intervals with a sign change give all m roots, all positive.
    assert all(0 < a < b < 1 for a,b in intervals)
    dp = sp.simplify(p[m+1].subs(s, shift)-p[m+1].subs(s, 0))
    assert dp != 0
    return {
        "m": m, "shift": str(shift),
        "base_roots": [str(u) for u in roots],
        "new_polynomial_descending_coefficients": [str(c) for c in candidate.all_coeffs()],
        "isolating_intervals": [[str(a),str(b)] for a,b in intervals],
        "p1_change": str(shift), "first_changed_higher_power_sum": m+1,
        "higher_power_sum_change": str(dp),
        "verified_equal_power_sums": list(range(2,m+1)),
    }

def verify_shifted_inequality() -> int:
    rng = random.Random(20260929)
    count = 0
    for m in range(1, 8):
        for r in range(4):
            for _ in range(250):
                x = sorted(Fraction(rng.randrange(17),16) for _ in range(m))
                y = sorted(Fraction(rng.randrange(17),16) for _ in range(m))
                h = max(abs(a-b) for a,b in zip(x,y))
                err = max(abs(sum(a**k for a in x)-sum(b**k for b in y))
                          for k in range(r+1,r+m+1))
                assert h**(m+r) <= 8**(m+r)*err
                count += 1
    return count

def verify_tangent_vectors() -> int:
    z = sp.symbols("z")
    count = 0
    for m in range(1,9):
        u = [sp.Rational(i,m+1) for i in range(1,m+1)]
        P = sp.prod(z-v for v in u)
        dP = sp.diff(P,z)
        for r in range(5):
            w = [1/(v**r*dP.subs(z,v)) for v in u]
            for j in range(1,m):
                assert sp.simplify(sum((r+j)*v**(r+j-1)*wi for v,wi in zip(u,w))) == 0
            assert sp.simplify(sum((r+m)*v**(r+m-1)*wi for v,wi in zip(u,w))) == r+m
            count += 1
    return count

def explicit_pair() -> dict:
    u = [sp.Integer(0),sp.Integer(5)]
    v = [sp.Integer(3),sp.Integer(4)]
    assert sum(a*a for a in u)==sum(a*a for a in v)==25
    assert sum(a**3 for a in u)-sum(a**3 for a in v)==34
    kappa6 = sp.Rational(16,63)
    coefficient = kappa6*34/sp.factorial(6)
    chi_coefficient = sp.factorial(6)*coefficient**2
    assert coefficient == sp.Rational(34,2835)
    return {"u_squared_scales":list(map(str,u)),"v_squared_scales":list(map(str,v)),
            "sixth_density_derivative_coefficient":str(coefficient),
            "chi_square_leading_constant_Z_zero_variance_one":str(chi_coefficient)}

def fourier_diagnostic() -> list[dict]:
    mp.mp.dps = 80
    def sinc_log(z: mp.mpf) -> mp.mpf:
        return mp.log(mp.sin(z)/z) if z else mp.mpf(0)
    rows=[]
    target=-mp.mpf(34)/2835
    for ts in ["0.2","0.1","0.05","0.025","0.0125"]:
        t=mp.mpf(ts)
        # Variance-compensated characteristic functions at frequency 1.
        log_u=-(1-5*t*t/3)/2+sinc_log(mp.sqrt(5)*t)
        log_v=-(1-7*t*t/3)/2+sinc_log(mp.sqrt(3)*t)+sinc_log(2*t)
        ratio=(log_u-log_v)/t**6
        rows.append({"t":ts,"log_characteristic_difference_div_t6":mp.nstr(ratio,35),
                     "limit":mp.nstr(target,35),"absolute_error":mp.nstr(abs(ratio-target),15)})
    return rows

def main() -> None:
    flows=[exact_shift_flow(m) for m in range(1,9)]
    tests=verify_shifted_inequality()
    tangents=verify_tangent_vectors()
    pair=explicit_pair()
    numeric=fourier_diagnostic()
    results={"seed":20260929,"rational_inequality_tests":tests,
             "exact_tangent_checks":tangents,"flow_certificates":flows,
             "explicit_two_factor_pair":pair,"fourier_diagnostic":numeric,
             "status":"All exact checks passed; numerical diagnostics are not rigorous interval bounds."}
    (OUT/"verification_results.json").write_text(json.dumps(results,indent=2)+"\n")
    summary=(f"PASS: {tests} exact rational shifted-moment inequalities.\n"
             f"PASS: {tangents} exact generalized-Vandermonde tangent checks.\n"
             "PASS: 8 exact first-moment flows, each with rational all-positive-root certificates.\n"
             "PASS: explicit m=2 moment and leading-coefficient identities.\n"
             f"m=2 chi-square leading coefficient, Z=0 and base variance 1: {pair['chi_square_leading_constant_Z_zero_variance_one']}\n"
             "Fourier checks: 80-digit arithmetic, not interval-certified.\n"
             "These checks do not constitute a Lean/Rocq proof or a proof of all parameter values.\n")
    (OUT/"verification_summary.txt").write_text(summary)
    print(summary)
    for row in numeric:
        print(row["t"], row["log_characteristic_difference_div_t6"])

if __name__ == "__main__":
    main()
