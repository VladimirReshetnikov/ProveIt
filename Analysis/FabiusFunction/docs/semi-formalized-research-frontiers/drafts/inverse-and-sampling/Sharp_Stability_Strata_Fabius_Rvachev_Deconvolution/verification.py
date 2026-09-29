#!/usr/bin/env python3
"""Exact algebraic checks and high-precision diagnostics for article.tex.

These tests are not a formal verification of the analytical theorems.  In
particular, the numerical experiments measure characteristic functions at
one frequency, not total variation distances.

Usage: python verification.py --output-dir .
Requires Python >= 3.10, SymPy and mpmath.
"""
from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path
import platform
from typing import Sequence

import mpmath as mp
import sympy as sp

z = sp.Symbol("z")


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def power_sums(poly: sp.Poly, count: int) -> list[sp.Expr]:
    """Newton sums of a monic polynomial, including orders above its degree."""
    require(poly.LC() == 1, "Polynomial must be monic")
    n = poly.degree()
    coeff = poly.all_coeffs()
    sums: list[sp.Expr] = [sp.Integer(n)]
    for k in range(1, count + 1):
        if k <= n:
            value = -sum(coeff[j] * sums[k-j] for j in range(1, k)) - k*coeff[k]
        else:
            value = -sum(coeff[j] * sums[k-j] for j in range(1, n+1))
        sums.append(sp.factor(value))
    return sums


def polynomial_from_sums(sums: Sequence[sp.Expr]) -> sp.Poly:
    """Reconstruct a degree-r polynomial from s_1,...,s_r."""
    r = len(sums)
    e: list[sp.Expr] = [sp.Integer(1)]
    for j in range(1, r+1):
        e.append(sp.factor(sum((-1)**(k-1)*e[j-k]*sums[k-1]
                               for k in range(1, j+1))/j))
    return sp.Poly(sum((-1)**j*e[j]*z**(r-j) for j in range(r+1)), z)


def uniform_cumulant(k: int) -> sp.Expr:
    return 2**(2*k)*sp.bernoulli(2*k)/(2*k)


def moments_from_cumulants(kappa: Sequence[sp.Expr]) -> list[sp.Expr]:
    nmax = len(kappa)-1
    moments = [sp.Integer(1)]
    for n in range(1, nmax+1):
        moments.append(sp.factor(sum(sp.binomial(n-1,j-1)*kappa[j]*moments[n-j]
                                     for j in range(1,n+1))))
    return moments


def cumulants_from_moments(moments: Sequence[sp.Expr]) -> list[sp.Expr]:
    kappa = [sp.Integer(0)]
    for n in range(1,len(moments)):
        kappa.append(sp.factor(moments[n]-sum(sp.binomial(n-1,j-1)*kappa[j]*moments[n-j]
                                               for j in range(1,n))))
    return kappa


def exact_checks(out: Path) -> dict:
    rows = []
    for m in range(1,13):
        scale = sp.Rational(1, 2**(m-1))
        qplus = sp.Poly(scale*(sp.chebyshevt(m,z)-sp.Rational(1,2)), z)
        qminus = sp.Poly(scale*(sp.chebyshevt(m,z)+sp.Rational(1,2)), z)
        splus, sminus = power_sums(qplus,m), power_sums(qminus,m)
        expected = m*scale
        require(all(splus[k] == sminus[k] for k in range(1,m)), f"m={m}: cancellation")
        require(splus[m]-sminus[m] == expected, f"m={m}: leading gap")
        shifted_plus = sp.Poly(qplus.as_expr().subs(z,z-2),z)
        shifted_minus = sp.Poly(qminus.as_expr().subs(z,z-2),z)
        uplus, uminus = power_sums(shifted_plus,m), power_sums(shifted_minus,m)
        require(all(uplus[k] == uminus[k] for k in range(1,m)), f"m={m}: shifted cancellation")
        require(uplus[m]-uminus[m] == expected, f"m={m}: shifted leading gap")
        require(sp.gcd(qplus,qplus.diff()).degree() == 0, f"m={m}: plus simplicity")
        require(sp.gcd(qminus,qminus.diff()).degree() == 0, f"m={m}: minus simplicity")
        require(sp.gcd(qplus,qminus).degree() == 0, f"m={m}: disjoint root sets")
        density_coefficient = sp.factor(uniform_cumulant(m)*expected/sp.factorial(2*m))
        rows.append({"m":m,"D_m":str(expected),"uniform_cumulant_2m":str(uniform_cumulant(m)),
                     "signed_density_coefficient":str(density_coefficient),"exact_checks":"PASS"})
    with (out/"data"/"chebyshev_checks.csv").open("w",newline="") as f:
        writer=csv.DictWriter(f,fieldnames=list(rows[0]))
        writer.writeheader(); writer.writerows(rows)

    recovered = []
    for r in range(1,9):
        # Includes zero slots, repetitions, and distinct rational squared scales.
        p = [sp.Rational((j*j+2*j) % 7,5) for j in range(r)]
        kap = [sp.Integer(0)]*(2*r+1)
        for k in range(1,r+1):
            kap[2*k] = uniform_cumulant(k)*(sp.Rational(1,4**k-1)+sum(x**k for x in p))
        moments = moments_from_cumulants(kap)
        back = cumulants_from_moments(moments)
        require(back == kap,f"r={r}: moment/cumulant round trip")
        recovered_s = [sp.factor(back[2*k]/uniform_cumulant(k)-sp.Rational(1,4**k-1))
                       for k in range(1,r+1)]
        recovered_poly = polynomial_from_sums(recovered_s)
        true_poly = sp.Poly(sp.prod(z-x for x in p),z)
        require(recovered_poly == true_poly,f"r={r}: exact polynomial recovery")
        recovered.append({"r":r,"squared_scales":[str(x) for x in p],
                          "recovered_polynomial":str(recovered_poly.as_expr())})
    return {"chebyshev_orders_checked":list(range(1,13)),
            "exact_moment_recovery_examples":recovered,
            "uniform_cumulants_first_three":[str(uniform_cumulant(k)) for k in (1,2,3)]}


def sinc(x: mp.mpf) -> mp.mpf:
    return mp.sin(x)/x if x else mp.mpf(1)


def chebyshev_roots(m: int, level: mp.mpf) -> list[mp.mpf]:
    alpha = mp.acos(level)
    return sorted(mp.cos((alpha+2*mp.pi*k)/m) for k in range(m))


def numerical_diagnostics(out: Path) -> dict:
    mp.mp.dps = 100
    xi = mp.mpf("0.9")
    # The fixed 220-factor prefix is used only as a common smooth multiplier
    # in this pointwise diagnostic. Its omitted log-tail is < 10^-132 here.
    background = mp.fprod(sinc(xi/mp.mpf(2)**j) for j in range(1,221))
    rows = []
    last_slopes = {}
    for m in (3,5):
        xp = chebyshev_roots(m,mp.mpf("0.5"))
        xm = chebyshev_roots(m,mp.mpf("-0.5"))
        for regime in ("positive_collision","vanishing_cluster"):
            previous = None
            for ell in range(3,13):
                t=mp.mpf(2)**(-ell)
                if regime == "positive_collision":
                    ap=[mp.sqrt(1+t*x) for x in xp]
                    am=[mp.sqrt(1+t*x) for x in xm]
                    expected=m
                else:
                    ap=[t*mp.sqrt(2+x) for x in xp]
                    am=[t*mp.sqrt(2+x) for x in xm]
                    expected=2*m
                phi_p=background*mp.fprod(sinc(xi*a) for a in ap)
                phi_m=background*mp.fprod(sinc(xi*a) for a in am)
                gap=abs(phi_p-phi_m)
                distance=max(abs(a-b) for a,b in zip(ap,am))
                require(gap>0,"Precision loss in pointwise Fourier diagnostic")
                slope=mp.log(previous/gap,2) if previous is not None else None
                rows.append({"m":m,"regime":regime,"ell":ell,"t":mp.nstr(t,22),
                             "amplitude_distance":mp.nstr(distance,30),
                             "fourier_gap_at_0.9":mp.nstr(gap,30),
                             "halving_slope":"" if slope is None else mp.nstr(slope,20),
                             "predicted_power":expected})
                previous=gap
            require(abs(slope-expected)<mp.mpf("0.005"),f"Unexpected scaling: {regime},m={m}")
            last_slopes[f"{regime}_m{m}"]=mp.nstr(slope,20)
    with (out/"data"/"sharpness_scaling.csv").open("w",newline="") as f:
        writer=csv.DictWriter(f,fieldnames=list(rows[0]))
        writer.writeheader(); writer.writerows(rows)
    return {"decimal_precision":100,"frequency":"0.9","background_prefix_terms":220,
            "last_halving_slopes":last_slopes,
            "warning":"Pointwise Fourier diagnostics, not numerical TV distances and not a proof."}


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir",type=Path,default=Path(__file__).resolve().parent)
    args=parser.parse_args()
    args.output_dir.mkdir(parents=True,exist_ok=True)
    (args.output_dir/"data").mkdir(exist_ok=True)
    results={"status":"PASS","python":platform.python_version(),"sympy":sp.__version__,
             "mpmath":mp.__version__,"exact":exact_checks(args.output_dir),
             "numerical":numerical_diagnostics(args.output_dir)}
    (args.output_dir/"verification_results.json").write_text(json.dumps(results,indent=2)+"\n")
    print(json.dumps(results,indent=2))


if __name__ == "__main__":
    main()
