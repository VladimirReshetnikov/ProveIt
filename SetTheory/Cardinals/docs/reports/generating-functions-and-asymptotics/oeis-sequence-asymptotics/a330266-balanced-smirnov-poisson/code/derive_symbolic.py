#!/usr/bin/env python3
"""Symbolically recover the first four factorial cumulants.

Requires SymPy.  The script prints exact expressions and checks the displayed
n^{-3} logarithmic expansion in article.tex.
"""

from __future__ import annotations

import sympy as sp


def main() -> None:
    k, n, v, z, t = sp.symbols("k n v z t", positive=True)
    N = k * n

    a = []
    for m in range(5):
        falling_k = sp.prod(k - j for j in range(m))
        falling_km1 = sp.prod(k - 1 - j for j in range(m))
        a.append(sp.factor(falling_k * falling_km1 / sp.factorial(m)))

    R = sum(a[m] * (v * z) ** m for m in range(5))
    power = sp.series(R**n, v, 0, 5).removeO().expand()
    phi = 0
    for m in range(5):
        coefficient = power.coeff(v, m).coeff(z, m)
        falling_N = sp.prod(N - j for j in range(m))
        phi += coefficient * v**m / falling_N

    log_phi = sp.series(sp.log(phi), v, 0, 5).removeO().expand()
    cumulants = [
        sp.factor(sp.diff(log_phi, v, r).subs(v, 0)) for r in range(1, 5)
    ]
    for r, expression in enumerate(cumulants, 1):
        print(f"kappa_{r}^F = {expression}")

    lam = k - 1
    displayed = (
        lam * v
        - lam**2 * v**2 / (2 * k * n)
        + lam**2 * v**2 * (2 * (k - 2) * v - 3) / (6 * k**2 * n**2)
        - lam**2
        * v**2
        * ((k**2 - 6 * k + 7) * v**2 - 4 * (k - 2) * v + 2)
        / (4 * k**3 * n**3)
    )

    truncated_from_cumulants = sum(
        cumulants[r - 1] * v**r / sp.factorial(r) for r in range(1, 5)
    )
    difference = sp.series(
        (truncated_from_cumulants - displayed).subs(n, 1 / t), t, 0, 4
    ).removeO()
    assert sp.simplify(difference) == 0
    print("The n^{-3} logarithmic expansion is verified exactly.")


if __name__ == "__main__":
    main()
