#!/usr/bin/env python3
"""Finite sanity checks for the accompanying research article.

These tests check identities, examples, and finite congruence ranges.
They do NOT formally verify the quantified theorems over Hahn fields.
Requires Python 3.10+ and SymPy. Writes only to an explicitly chosen path.
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("Install SymPy first: python -m pip install sympy") from exc


def H(value: int) -> int:
    """The classical intersective polynomial, evaluated exactly."""
    square = value * value
    return (square - 13) * (square - 17) * (square - 221)


def pell_mod_order(modulus: int) -> int:
    """Order of 3+2*T in (Z/nZ)[T]/(T^2-2), by finite enumeration."""
    if modulus < 1:
        raise ValueError("The modulus must be positive")
    if modulus == 1:
        return 1
    u, v = 1, 0
    for index in range(1, modulus * modulus + 1):
        u, v = (3 * u + 4 * v) % modulus, (2 * u + 3 * v) % modulus
        if u == 1 and v == 0:
            return index
    raise AssertionError(f"No unit order found within n^2 for n={modulus}")


def pell_divisible(modulus: int) -> tuple[int, int, int]:
    """Return a positive integer Pell solution whose v is divisible by n."""
    if modulus < 1:
        raise ValueError("The modulus must be positive")
    u, v = 1, 0
    for index in range(1, modulus * modulus + 1):
        u, v = 3 * u + 4 * v, 2 * u + 3 * v
        if v % modulus == 0:
            assert u * u - 2 * v * v == 1 and v > 0
            return index, u, v
    raise AssertionError("Pell divisibility bound failed")


def modular_root(modulus: int) -> int:
    if modulus < 1:
        raise ValueError("The modulus must be positive")
    for value in range(modulus):
        if H(value) % modulus == 0:
            return value
    raise AssertionError(f"H has no root modulo {modulus}")


def check_all(pell_limit: int, root_limit: int) -> dict[str, Any]:
    x, u, v, w, s1, s2, s3, s4 = sp.symbols("x u v w s1 s2 s3 s4")
    witnesses = (u, v, w, s1, s2, s3, s4)
    variables = (x,) + witnesses
    P = x * ((u**2 - 2*v**2 - 1)**2 + (v - x*w)**2
             + (u - 2 - s1**2 - s2**2 - s3**2 - s4**2)**2)
    poly = sp.Poly(P, *variables)
    assert poly.total_degree() == 5
    assert len(witnesses) == 7
    n, y = sp.symbols("n y")
    CT = P.subs(x, n)**2 + ((x-n)**2 - 2*y**2)**2
    ct_poly = sp.Poly(CT, x, n, *witnesses, y)
    assert ct_poly.total_degree() == 10

    real_examples = [
        (1, 3, 2, 2, 1, 0, 0, 0),
        (2, 3, 2, 1, 1, 0, 0, 0),
        (3, 17, 12, 4, 3, 2, 1, 1),
        (-3, 17, 12, -4, 3, 2, 1, 1),
        (5, 99, 70, 14, 9, 4, 0, 0),
        (7, 99, 70, 10, 9, 4, 0, 0),
    ]
    for values in real_examples:
        assert sp.expand(P.subs(dict(zip(variables, values)))) == 0
    assert sp.expand(P.subs(x, 0)) == 0

    orders = [pell_mod_order(m) for m in range(1, pell_limit + 1)]
    roots = [modular_root(m) for m in range(1, root_limit + 1)]

    # Symbolic verification of the exact four-square identity in Appendix A.
    a, b, c, d, r, ss, t, uu = sp.symbols("a b c d r ss t uu")
    components = [a*r+b*ss+c*t+d*uu, -a*ss+b*r-c*uu+d*t,
                  -a*t+b*uu+c*r-d*ss, -a*uu-b*t+c*ss+d*r]
    expected = (a*a+b*b+c*c+d*d) * (r*r+ss*ss+t*t+uu*uu)
    assert sp.expand(sum(term**2 for term in components) - expected) == 0

    # Gaussian system degrees, with no sum-of-squares combination.
    h, rr = sp.symbols("h rr")
    HH = (rr**2-13)*(rr**2-17)*(rr**2-221)
    gaussian_system = [x*(u**2-2*v**2-1), x*(v-x*w), x*(v*h-HH)]
    gaussian_degrees = [sp.Poly(eq, x, u, v, w, h, rr).total_degree()
                        for eq in gaussian_system]
    assert gaussian_degrees == [3, 3, 7]
    gaussian_examples = []
    for aa, bb in [(1, 1), (2, 1), (3, 0), (-1, 2), (0, 1), (3, 3)]:
        norm = aa*aa + bb*bb
        index, pu, pv = pell_divisible(norm)
        xx = aa + sp.I*bb
        ww = (pv // norm)*(aa - sp.I*bb)
        root = modular_root(pv)
        hh = H(root) // pv
        substitutions = {x: xx, u: pu, v: pv, w: ww, h: hh, rr: root}
        assert all(sp.expand(eq.subs(substitutions)) == 0 for eq in gaussian_system)
        gaussian_examples.append({"x": str(xx), "pell_index": index,
                                  "u": pu, "v": pv, "w": str(ww),
                                  "h": hh, "r": root})
    assert H(1) == -42240

    # Exact finite-support checks (X models omega; not a full Hahn implementation).
    X = sp.symbols("X")
    samples = [sp.pi*X**3-sp.sqrt(3)*X, X**2+sp.I*X, -X, sp.Integer(0)]
    for value in samples:
        assert sp.expand(value**2 - 2*(value/sp.sqrt(2))**2) == 0
    value = sp.pi*X**3-sp.sqrt(3)*X+3
    assert sp.expand((value-3)**2 - 2*((value-3)/sp.sqrt(2))**2) == 0

    def twist(expr: Any) -> Any:
        pp = sp.Poly(expr, X)
        return sp.expand(sum(coeff * sp.I**exponent[0] * X**exponent[0]
                             for exponent, coeff in pp.terms()))

    f = (2+sp.I)*X**3 + sp.sqrt(2)*X + 7
    g = (3-sp.I)*X**2 + 2*X - 4*sp.I
    assert sp.expand(twist(f*g) - twist(f)*twist(g)) == 0
    assert sp.expand(twist(f+g) - twist(f) - twist(g)) == 0
    assert twist(X) == sp.I*X
    assert twist(sp.Integer(7)) == 7

    return {
        "status": "all finite checks passed",
        "scope": "sanity checks only; not a proof assistant verification",
        "python_version": sys.version.split()[0],
        "sympy_version": sp.__version__,
        "real_standard_polynomial": {"total_degree": 5, "free_variables": 1,
                                      "existential_variables": 7,
                                      "expanded_monomials": len(poly.terms()),
                                      "displayed_nonzero_examples_checked": len(real_examples),
                                      "zero_guard_checked": True},
        "real_constant_term_polynomial": {"total_degree": 10,
                                           "free_variables": 2,
                                           "existential_variables": 8},
        "gaussian_standard_system": {"equations": 3,
                                      "total_degrees": gaussian_degrees,
                                      "existential_variables": 5,
                                      "examples": gaussian_examples},
        "pell_modular_tests": {"all_moduli_from": 1, "through": pell_limit,
                               "all_orders_bounded_by_n_squared": True,
                               "largest_order_seen": max(orders)},
        "intersective_polynomial_tests": {"all_moduli_from": 1,
                                          "through": root_limit,
                                          "largest_least_root_seen": max(roots)},
        "four_square_product_identity": "symbolically verified",
        "finite_support_ideal_identities": "symbolically verified",
        "finite_support_character_twist": "addition and multiplication verified",
        "not_tested": ["all infinite supports", "class-sized interpretations",
                       "formal first-order proofs", "historical priority"]
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        help="Optional JSON output path; otherwise print to stdout")
    parser.add_argument("--pell-limit", type=int, default=500)
    parser.add_argument("--root-limit", type=int, default=2000)
    args = parser.parse_args()
    if args.pell_limit < 1 or args.root_limit < 1:
        parser.error("Both limits must be positive")
    result = check_all(args.pell_limit, args.root_limit)
    text = json.dumps(result, indent=2, ensure_ascii=False) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
        print(f"{result['status']}; output: {args.output}")
    else:
        print(text, end="")


if __name__ == "__main__":
    main()
