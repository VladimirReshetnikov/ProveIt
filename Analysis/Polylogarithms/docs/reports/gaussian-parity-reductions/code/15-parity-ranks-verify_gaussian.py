#!/usr/bin/env python3
"""Independent quadrature audit of the proved Gaussian parity reductions.

The numerical values use a one-dimensional iterated-integral representation,
not the Bernoulli reduction. Running this script reproduces 23 checks at
65 decimal digits by default and also verifies the five manuscript equations
by exact symbolic subtraction. The checks support the proof; they do not
replace it.

    python code/verify_gaussian.py
    python code/verify_gaussian.py --dps 65 --output results/gaussian_checks.json

Dependencies: Python >=3.10, SymPy >=1.12, mpmath >=1.3.
"""
from __future__ import annotations
import argparse
import json
import math
from pathlib import Path
import mpmath as mp
import sympy as sp
from gaussian_parity import ELL, beta, zeta, gaussian_component, verify_weight_six


def direct_double(a, b, z):
    """F_ab(z)=z/(a-1)! integral_0^1 (-log x)^(a-1) Li_b(zx)/(1-zx) dx."""
    def integrand(x):
        return (-mp.log(x))**(a-1) * mp.polylog(b, z*x) / (1-z*x)
    return z*mp.quad(integrand, [0, mp.mpf("0.1"), mp.mpf("0.5"), 1]) / mp.factorial(a-1)


def numerical_expression(expression):
    substitutions = {ELL: sp.Float(str(mp.log(2)), mp.mp.dps+5)}
    for n in range(2, 14):
        substitutions[beta(n)] = sp.Float(str(mp.im(mp.polylog(n, 1j))), mp.mp.dps+5)
        if n % 2:
            substitutions[zeta(n)] = sp.Float(str(mp.zeta(n)), mp.mp.dps+5)
    return mp.mpf(str(expression.subs(substitutions).evalf(mp.mp.dps-1)))


def general_rhs(a, b, theta):
    z, w = mp.exp(1j*theta), a+b
    def bernoulli(n):
        return (2*mp.pi*1j)**n/mp.factorial(n)*mp.bernpoly(n, theta/(2*mp.pi))
    ans = -mp.polylog(w, z)-bernoulli(w)
    ans -= sum((-1)**k*math.comb(a+k-1, k)*bernoulli(b-k)*mp.polylog(a+k, z)
               for k in range(b+1))
    ans += (-1)**(b+1)*sum(math.comb(b+k-1, b-1)*mp.zeta(b+k)*bernoulli(a-k)
                           for k in range(1, a+1))
    return ans


def run_checks():
    results = []
    errors = []
    tolerance = mp.mpf(10)**(-(mp.mp.dps-6))
    for w in (4, 5, 6, 8):
        for a in range(1, w):
            b = w-a
            value = direct_double(a, b, 1j)
            direct = mp.im(value) if w % 2 == 0 else mp.re(value)
            predicted = numerical_expression(gaussian_component(a, b))
            error = abs(direct-predicted)
            assert error < tolerance, (a, b, error)
            errors.append(error)
            record = {"a": a, "b": b, "part": "imag" if w % 2 == 0 else "real",
                      "direct": mp.nstr(direct, mp.mp.dps-9),
                      "abs_error": mp.nstr(error, 6)}
            results.append(record)
            print(json.dumps(record), flush=True)
    for a, b, angle in ((1, 1, "0.4"), (1, 3, "2.1"), (3, 2, "4.3"), (4, 3, "5.7")):
        theta = mp.mpf(angle)
        value = direct_double(a, b, mp.exp(1j*theta))
        lhs = value-(-1)**(a+b)*mp.conj(value)
        error = abs(lhs-general_rhs(a, b, theta))
        assert error < tolerance, (a, b, theta, error)
        errors.append(error)
        record = {"a": a, "b": b, "theta": angle, "abs_error": mp.nstr(error, 6)}
        results.append(record)
        print(json.dumps(record), flush=True)
    return {"mpmath_dps": mp.mp.dps, "count": len(results),
            "method": "independent one-dimensional iterated-integral quadrature",
            "threshold": mp.nstr(tolerance, 6), "max_abs_error": mp.nstr(max(errors), 6),
            "exact_weight_six": verify_weight_six(), "results": results}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dps", type=int, default=65)
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parents[1]
                        / "results" / "gaussian_checks.json")
    args = parser.parse_args()
    if args.dps < 30:
        parser.error("--dps must be at least 30")
    mp.mp.dps = args.dps
    results = run_checks()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(results, indent=2)+"\n", encoding="utf-8")
    print(f"All {results['count']} checks passed; max error {results['max_abs_error']}.")
    print(args.output)


if __name__ == "__main__":
    main()
