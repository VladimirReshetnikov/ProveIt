#!/usr/bin/env python3
"""Generate all-order Bessel profile and zero coefficients exactly.

Requires SymPy. The construction uses Faulhaber's exact power sums, then
the scalar Bessel differential equation at a simple zero. All arithmetic
is rational-polynomial arithmetic. This is an executable coefficient
generator, not a numerical fit and not a substitute for the uniform
remainder proof in the article.
"""

import argparse
import json
from pathlib import Path

import sympy as s


def generate(order):
    t, w, k, D, z, r, lam = s.symbols("t w k D z r lambda")
    log_e = s.Integer(0)
    for m in range(1, order + 2):
        power_sum = (s.bernoulli(m + 1, k + 1) - s.bernoulli(m + 1, 1)) / (m + 1)
        log_e += (-1) ** (m - 1) * t ** m * w ** (2 * m) * power_sum.subs(k, 1 / w) / m
    log_e = s.expand(log_e)
    log_coeff = [s.expand(log_e.coeff(w, j)) for j in range(order + 1)]
    assert log_coeff[0] == t / 2
    e_coeff = [s.Integer(1)]
    for j in range(1, order + 1):
        e_coeff.append(s.expand(sum(m * log_coeff[m] * e_coeff[j - m]
                                    for m in range(1, j + 1)) / j))

    def d_minus_c(pair, c):
        """Apply z*d/dz-r-c, using z*Psi''+(1-r)*Psi'+Psi/2=0."""
        A, B = pair
        return (s.expand(z * s.diff(A, z) - (r + c) * A - B / 2),
                s.expand(z * A + z * s.diff(B, z) - (1 + c) * B))

    operators, reduced = [], []
    for poly in e_coeff:
        operator, A, B = s.Integer(0), s.Integer(0), s.Integer(0)
        for (degree,), coefficient in s.Poly(poly, t).terms():
            falling = s.prod(D - j for j in range(degree))
            operator += coefficient * 2 ** degree * falling
            pair = (s.Integer(1), s.Integer(0))
            for j in range(degree):
                pair = d_minus_c(pair, j)
            A += coefficient * 2 ** degree * pair[0]
            B += coefficient * 2 ** degree * pair[1]
        operators.append(s.factor(operator))
        reduced.append((s.expand(A), s.expand(B)))

    # Values of Psi^(j)(lambda)/Psi'(lambda), with Psi(lambda)=0.
    u = [s.Integer(0), s.Integer(1)]
    for j in range(order + 1):
        u.append(s.factor(-((j + 1 - r) * u[j + 1] + u[j] / 2) / lam))

    def profile_derivative(profile_order, derivative_order):
        A, B = reduced[profile_order]
        return s.factor(sum(s.binomial(derivative_order, h) * (
            s.diff(A, z, h).subs(z, lam) * u[derivative_order - h]
            + s.diff(B, z, h).subs(z, lam) * u[derivative_order - h + 1])
            for h in range(derivative_order + 1)))

    derivatives = {(j, p): profile_derivative(j, p)
                   for j in range(order + 1)
                   for p in range(order + 1 - j)}
    root_coeff, delta = [], s.Integer(0)
    for q in range(1, order + 1):
        equation = sum(w ** j * derivatives[j, p] * delta ** p / s.factorial(p)
                       for j in range(q + 1) for p in range(q + 1 - j))
        coefficient = s.factor(-s.expand(equation).coeff(w, q))
        root_coeff.append(coefficient)
        delta += coefficient * w ** q
    assert s.simplify(root_coeff[0] + (2 * r + 5) * lam / 3) == 0
    if order >= 2:
        assert s.simplify(root_coeff[1] - lam * (4 * r * r + 15 * r + lam + 20) / 9) == 0
        assert s.simplify(e_coeff[2] - (-t ** 2 / 8 + t ** 4 / 72)) == 0
    return {
        "status": "exact rational-polynomial generation completed",
        "sympy_version": s.__version__, "order": order,
        "notation": {"D": "z*d/dz-r", "lambda": "j_(abs(r),m)^2/2",
                     "z_zero": "lambda + sum_j root_coefficients[j-1]/k^j"},
        "exponential_product_coefficients": [str(p) for p in e_coeff],
        "profile_operators": [str(p) for p in operators],
        "root_coefficients": [str(p) for p in root_coeff],
        "root_coefficients_latex": [s.latex(p) for p in root_coeff],
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--order", type=int, default=4)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).parent / "evidence" / "bessel-coefficients.json")
    args = parser.parse_args()
    if args.order < 1:
        parser.error("--order must be positive")
    result = generate(args.order)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(result["status"])
    for j, coefficient in enumerate(result["root_coefficients"], 1):
        print(f"k^(-{j}): {coefficient}")


if __name__ == "__main__":
    main()
