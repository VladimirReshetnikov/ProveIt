#!/usr/bin/env python3
"""Generate the Lambert-W-coordinate critical-temperature inverse.

Write T/T0 = 1 + sum(c_k(w) z**k), z=delta/sqrt(T0), and D=w+1.
The exact equation is

 D*u + sum_{j>=2} (-1)**j*u**j/(j*(j-1))
     + sum_{k>=1} b_k*z**k*(1+u)**(1-k/2) = 0.

This script uses finite rational polynomial arithmetic.  It substitutes
b2=-1/16 and b6=0, and retains the remaining analytic constants as symbols.
It checks the generated answer by substitution through the requested order.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import sympy as sp


def generate(order=6):
    if not isinstance(order, int) or order < 1:
        raise ValueError("order must be a positive integer")
    w, h = sp.symbols("w h")
    bs = {k: sp.symbols(f"b{k}") for k in range(1, order + 1)}
    if order >= 2:
        bs[2] = -sp.Rational(1, 16)
    for k in range(6, order + 1, 4):
        bs[k] = sp.S.Zero

    # Work polynomially in h=1/(w+1); expanding rational expressions in
    # w during every intermediate operation causes avoidable expression
    # growth.  Lists represent finite z-polynomials.
    def multiply(a, b):
        answer = [sp.S.Zero] * (order + 1)
        for i, ai in enumerate(a):
            if ai == 0:
                continue
            for j, bj in enumerate(b[:order+1-i]):
                if bj != 0:
                    answer[i+j] += ai*bj
        return [sp.expand(x) for x in answer]

    def nonlinear(u):
        powers = [[sp.S.One] + [sp.S.Zero]*order, u]
        for j in range(2, order+1):
            powers.append(multiply(powers[-1], u))
        result = [sp.S.Zero]*(order+1)
        for j in range(2, order+1):
            factor = sp.Rational((-1)**j, j*(j-1))
            for k in range(order+1):
                result[k] += factor*powers[j][k]
        for k in range(1, order+1):
            if bs[k] == 0:
                continue
            for j in range(order-k+1):
                factor = bs[k]*sp.binomial(1-sp.Rational(k, 2), j)
                for ell in range(order-k+1):
                    result[k+ell] += factor*powers[j][ell]
        return [sp.expand(x) for x in result]

    u = [sp.S.Zero]*(order+1)
    for n in range(1, order+1):
        u[n] = sp.expand(-h*nonlinear(u)[n])
    # Each coefficient is checked exactly rather than numerically.
    final = nonlinear(u)
    checks = {k: bool(sp.expand(u[k]/h + final[k]) == 0)
              for k in range(order+1)}
    coefficients = {k: sp.factor(u[k].subs(h, 1/(w+1)))
                    for k in range(1, order+1)}
    if not all(checks.values()):
        raise ArithmeticError("Symbolic substitution failed")
    return w, coefficients, checks


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--order", type=int, default=6)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1] / "data" / "inverse_coefficients.json")
    args = parser.parse_args()
    _, coefficients, checks = generate(args.order)
    output = {
        "coordinate": "T/T0 = 1 + sum c_k(w) z^k; z=delta/sqrt(T0), w=W0(8 exp(pi/2) b/delta^2), T0=b/w",
        "constants": "b_k=(-1)^k Gamma(1/4+k/2) zeta(1-k/2)/(Gamma(1/4) k!); b2=-1/16; b6,b10,...=0",
        "order": args.order,
        "all_exact_substitution_checks_pass": all(checks.values()),
        "coefficients": {str(k): {"sympy": str(v), "latex": sp.latex(v)}
                         for k, v in coefficients.items()},
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=2) + "\n", encoding="utf-8")
    print(f"Generated and exactly checked coefficients through order {args.order}.")
    print(args.output)


if __name__ == "__main__":
    main()

