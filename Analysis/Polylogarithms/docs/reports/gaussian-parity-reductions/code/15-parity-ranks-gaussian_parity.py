#!/usr/bin/env python3
"""Exact depth-two parity reductions at i, in descending-index convention.

F_{a,b}(z) = sum_{n>m>=1} z**n/(n**a*m**b).
The proved theorem is recorded in article.tex. It is a specialization of
known multiple-polylogarithm parity, independently proved there by
Bernoulli Fourier moments. No integer-relation search is used.

Examples:
    python code/gaussian_parity.py
    python code/gaussian_parity.py --max-weight 12 --output results/table.json

Dependencies: Python >=3.10, SymPy >=1.12.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import sympy as sp

ELL = sp.Symbol("ell", real=True)  # log(2)


def beta(n: int):
    """Formal beta(n) symbol; even arguments are used in reductions."""
    return sp.Symbol(f"beta{n}", real=True)


def zeta(n: int):
    """Even zeta values reduced exactly; odd values kept as formal symbols."""
    return sp.zeta(n) if n % 2 == 0 else sp.Symbol(f"zeta{n}", real=True)


def bernoulli_at_i(n: int):
    """C_n(pi/2)=(2*pi*i)^n B_n(1/4)/n!, including C_0=1."""
    return sp.expand((2 * sp.pi * sp.I) ** n * sp.bernoulli(n, sp.Rational(1, 4))
                     / sp.factorial(n))


def polylog_at_i(n: int):
    """Exact classical Li_n(i), with only even beta and odd zeta symbols."""
    re = -ELL / 2 if n == 1 else -(sp.Rational(1, 2) ** n) * (
        1 - sp.Rational(1, 2) ** (n - 1)) * zeta(n)
    im = beta(n) if n % 2 == 0 else -sp.im(bernoulli_at_i(n)) / 2
    return sp.expand(re + sp.I * im)


def parity_expression(a: int, b: int):
    """Exact RHS of F_ab(i)-(-1)^(a+b) F_ab(-i)."""
    if not isinstance(a, int) or not isinstance(b, int) or min(a, b) < 1:
        raise ValueError("a and b must be positive integers")
    w = a + b
    ans = -polylog_at_i(w) - bernoulli_at_i(w)
    ans -= sum((-1) ** k * sp.binomial(a + k - 1, k)
               * bernoulli_at_i(b - k) * polylog_at_i(a + k)
               for k in range(b + 1))
    ans += (-1) ** (b + 1) * sum(
        sp.binomial(b + k - 1, b - 1) * zeta(b + k) * bernoulli_at_i(a - k)
        for k in range(1, a + 1))
    return sp.expand(ans)


def gaussian_component(a: int, b: int):
    """Return Im F_ab(i) for even weight and Re F_ab(i) for odd weight."""
    p = parity_expression(a, b)
    if (a + b) % 2 == 0:
        assert sp.simplify(sp.re(p)) == 0, (a, b, sp.re(p))
        return sp.expand(sp.im(p) / 2)
    assert sp.simplify(sp.im(p)) == 0, (a, b, sp.im(p))
    return sp.expand(sp.re(p) / 2)


def manuscript_weight_six():
    """Independent transcription of chapter 04's five conjectural RHSs."""
    p = sp.pi
    return {
        (5, 1): (-64*p**3*zeta(3)-527*p*zeta(5)+4096*beta(6))/2048,
        (4, 2): (96*p**3*zeta(3)-32*p**2*beta(4)+1581*p*zeta(5)
                 -8448*beta(6))/1536,
        (3, 3): (-3*p**3*zeta(3)+64*p**2*beta(4)-1581*p*zeta(5)
                 +4608*beta(6))/1024,
        (2, 4): (-14*p**4*beta(2)+135*p**3*zeta(3)-1440*p**2*beta(4)
                 +23715*p*zeta(5)-69120*beta(6))/23040,
        (1, 5): (-150*p**5*ELL+56*p**4*beta(2)-270*p**3*zeta(3)
                 +1920*p**2*beta(4)-675*p*zeta(5))/92160,
    }


def verify_weight_six():
    for (a, b), expected in manuscript_weight_six().items():
        difference = sp.expand(gaussian_component(a, b) - expected)
        assert difference == 0, (a, b, difference)
    return {"identities": 5, "method": "exact symbolic subtraction", "status": "pass"}


def exact_table(max_weight: int):
    table = []
    for w in range(2, max_weight + 1):
        for a in range(w - 1, 0, -1):
            b = w - a
            expression = gaussian_component(a, b)
            table.append({"a": a, "b": b, "weight": w,
                          "component": "imag" if w % 2 == 0 else "real",
                          "expression": str(expression),
                          "latex": sp.latex(expression)})
    return table


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-weight", type=int, default=12)
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parents[1]
                        / "results" / "gaussian_parity_through_weight_12.json")
    args = parser.parse_args()
    if args.max_weight < 2:
        parser.error("--max-weight must be at least 2")
    checks = verify_weight_six()
    table = exact_table(args.max_weight)
    payload = {"convention": "F_ab(z)=sum_{n>m>=1} z^n/(n^a*m^b)",
               "symbols": {"ell": "log(2)", "betaN": "Dirichlet beta(N)",
                           "zetaN": "Riemann zeta(N)"},
               "max_weight": args.max_weight, "exact_checks": checks,
               "table": table}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(f"Saved {len(table)} exact parity reductions; all 5 manuscript checks passed.")
    print(args.output)


if __name__ == "__main__":
    main()
