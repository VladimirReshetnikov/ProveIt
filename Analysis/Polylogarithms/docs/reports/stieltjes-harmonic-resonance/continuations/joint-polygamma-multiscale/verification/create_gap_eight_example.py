"""Construct the exact convergent (p,q)=(14,22) identity from the theorem."""
from __future__ import annotations

import json
from pathlib import Path

import sympy as sp

from verify_gap_eight_bridge import late_matrix

ROOT = Path(__file__).resolve().parent


def centered_tail_coefficient(v, h):
    if h == 0:
        return sp.Rational(1, v - 1)
    return (sp.bernoulli(2 * h, sp.Rational(1, 2))
            * sp.rf(v, 2 * h - 1) / sp.factorial(2 * h))


def main():
    b, p, q = 11, 14, 22
    x = sp.Symbol("x")
    matrix = late_matrix(4, b)
    weights = list(matrix.inv()[0, :])
    kernel = sum(weights[t] * x**(2 * (b + t) + 1) for t in range(b))
    polynomial = sp.Poly(sp.expand(kernel.subs(x, x + sp.Rational(1, 2))
                                  - kernel.subs(x, x - sp.Rational(1, 2))), x)
    w = [polynomial.nth(2 * i) for i in range(q)]
    u = [sum(centered_tail_coefficient(p, e)
             * centered_tail_coefficient(q, h - e)
             for e in range(h + 1)) for h in range(6)]
    subtraction_coefficients = [
        sum(u[e] * w[q - 1 - h + e] for e in range(h + 1))
        for h in range(5)
    ]
    subtraction = sp.Poly(sum(subtraction_coefficients[h] * x**(8 - 2*h)
                              for h in range(5)), x)
    assert polynomial.degree() == 42 and subtraction.degree() == 8
    assert sp.Matrix(1, b, weights) * matrix == sp.eye(b)[0, :]
    laurent = sp.expand(polynomial.as_expr()
                        * sum(u[h] * x**(2 - p - q - 2*h) for h in range(6))
                        - subtraction.as_expr())
    assert all(term.as_powers_dict().get(x, 0) < 0
               for term in sp.Add.make_args(laurent))
    output = {
        "b": b, "p": p, "q": q, "P_degree": 42, "S_degree": 8,
        "K_odd_coefficients": [[2*(b+t)+1, str(weights[t])] for t in range(b)],
        "P_even_coefficients": [[2*t, str(w[t])] for t in range(q)],
        "S_even_coefficients": [[8-2*t, str(subtraction_coefficients[t])]
                                for t in range(5)],
        "first_omitted_laurent_coefficient": str(laurent.coeff(x, -2)),
        "inverse_row_verified": True, "centered_subtraction_verified": True,
        "sum": "-1/2", "convergence": "O((n+1/2)^(-2))",
    }
    path = ROOT / "gap_eight_14_22_example.json"
    path.write_text(json.dumps(output, indent=2) + "\n")
    print("Verified the inverse row and all nonnegative-power cancellations.")
    print("P leading coefficient:", w[-1])
    print("Wrote", path)


if __name__ == "__main__":
    main()
