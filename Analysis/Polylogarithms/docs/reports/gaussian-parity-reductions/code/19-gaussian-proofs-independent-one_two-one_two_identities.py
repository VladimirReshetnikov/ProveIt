"""Exact-formula and independent numerical checks for one-2 MPLs.

Conventions: Li_{s_1,...,s_d}(z) = sum_{n_1>...>n_d>=1}
z**n_1/(n_1**s_1 ... n_d**s_d). All logarithms use principal branches.

The closed formula is proved in the accompanying article. Quadrature and finite direct
nested sums are independent numerical implementations, not proof substitutes.
Run: python one_two_identities.py --digits 100 --output verification.json
"""

from __future__ import annotations

import argparse
import json
from math import comb, factorial
from pathlib import Path

import mpmath as mp


def one_two_closed(a: int, b: int, z):
    """Li_{1^a,2,1^b}(z) on C minus the nonnegative real axis."""
    if a < 0 or b < 0:
        raise ValueError("a and b must be nonnegative")
    n = a + b + 2
    w = 1 / (1 - z)
    ell = mp.log(w)
    value = sum(
        (-1) ** (a + k)
        * comb(k - 1, a)
        * ell ** (n - k)
        / factorial(n - k)
        * mp.polylog(k, w)
        for k in range(a + 1, n + 1)
    )
    value += (-1) ** (b + 1) * sum(
        comb(b + j + 1, j)
        * ell ** (a - j)
        / factorial(a - j)
        * mp.zeta(b + j + 2)
        for j in range(a + 1)
    )
    return value - ell**n / factorial(n)


def one_two_quadrature(a: int, b: int, z):
    """Evaluate the original iterated integral as a logarithmic moment."""
    qz = -mp.log1p(-z)

    def integrand(x):
        if not x:
            if b == 0:
                return qz**a * z
            return mp.mpc(0)
        qt = -mp.log1p(-z * x)
        return (qz - qt) ** a * qt ** (b + 1) / x

    return mp.quad(integrand, [0, mp.mpf(".25"), mp.mpf(".5"),
                               mp.mpf(".75"), 1]) / (
        factorial(a) * factorial(b + 1)
    )


def nested_sum(indices, z, terms=1000):
    """Direct nested series via harmonic prefix sums; require |z|<1."""
    if not abs(z) < 1:
        raise ValueError("finite-series comparison is for |z|<1")
    depth = len(indices)
    harmonic = [mp.mpf(0)] * depth + [mp.mpf(1)]
    value = mp.mpc(0)
    power = mp.mpc(1)
    for n in range(1, terms + 1):
        power *= z
        value += power * harmonic[1] / mp.mpf(n) ** indices[0]
        # Increasing j preserves the previous-n suffix sum harmonic[j+1].
        for j in range(depth):
            harmonic[j] += harmonic[j + 1] / mp.mpf(n) ** indices[j]
    return value


def gaussian_weight4_rhs():
    ell, pi, catalan = mp.log(2), mp.pi, mp.catalan
    w = (1 + 1j) / 2
    lam3, lam4 = mp.im(mp.polylog(3, w)), mp.im(mp.polylog(4, w))
    return [
        lam4 + ell * lam3 / 2
        - catalan * (pi**2 - 4 * ell**2) / 32
        - pi * (8 * ell**3 + 105 * mp.zeta(3)) / 768,
        -3 * lam4 - ell * lam3
        + catalan * (pi**2 - 4 * ell**2) / 32
        - 3 * pi**3 * ell / 256
        + pi * (2 * ell**3 + 67 * mp.zeta(3)) / 128,
        3 * lam4 + ell * lam3 / 2 + 5 * pi**3 * ell / 192
        - 163 * pi * mp.zeta(3) / 256,
    ]


def gaussian_height_rhs(p):
    ell, pi, catalan = mp.log(2), mp.pi, mp.catalan
    w = (1 + 1j) / 2
    lam = {k: mp.im(mp.polylog(k, w)) for k in range(3, 7)}
    mu = {k: mp.re(mp.polylog(k, w)) for k in (4, 5)}
    if p == 4:
        return (
            -lam[5] - ell * lam[4] / 2 + pi * mu[4] / 4
            + (pi**2 - 4 * ell**2) * lam[3] / 32
            + catalan * ell * (3 * pi**2 - 4 * ell**2) / 192
            + 35 * pi * ell * mp.zeta(3) / 512
            + pi * ell**2 * (ell**2 - pi**2) / 384
            - 17 * pi**5 / 92160
        )
    if p == 5:
        return (
            lam[6] + ell * lam[5] / 2 - pi * mu[5] / 4
            + (4 * ell**2 - pi**2) * lam[4] / 32
            - pi * ell * mu[4] / 8
            + ell * (4 * ell**2 - 3 * pi**2) * lam[3] / 192
            + catalan * (16 * ell**4 - 24 * ell**2 * pi**2 + pi**4) / 6144
            + 35 * pi * (pi**2 - 12 * ell**2) * mp.zeta(3) / 24576
            + pi * ell**3 * (5 * pi**2 - 3 * ell**2) / 5760
        )
    raise ValueError("only the explicit p=4 and p=5 rows are tabulated")


def run_verification(digits=100):
    mp.mp.dps = digits
    records = []
    points = [("gaussian", mp.j), ("eisenstein", (-1 + mp.j * mp.sqrt(3)) / 2),
              ("disk", (mp.mpf(3) + 2 * mp.j) / 10),
              ("negative", -mp.mpf(".6"))]
    for name, z in points:
        for n in range(2, 9):
            for a in range(n - 1):
                b = n - a - 2
                closed = one_two_closed(a, b, z)
                integral = one_two_quadrature(a, b, z)
                record = {
                    "point": name, "weight": n, "a": a, "b": b,
                    "closed_real": mp.nstr(mp.re(closed), digits),
                    "closed_imag": mp.nstr(mp.im(closed), digits),
                    "quadrature_residual": mp.nstr(abs(closed - integral), 8),
                }
                if name in ("disk", "negative") and n <= 6:
                    series = nested_sum((1,) * a + (2,) + (1,) * b, z)
                    record["series_residual"] = mp.nstr(abs(closed - series), 8)
                records.append(record)
    explicit = []
    for a, rhs in enumerate(gaussian_weight4_rhs()):
        lhs = mp.im(one_two_quadrature(a, 2 - a, mp.j))
        explicit.append({"row": f"gaussian_weight4_a{a}",
                         "lhs": mp.nstr(lhs, digits),
                         "rhs": mp.nstr(rhs, digits),
                         "residual": mp.nstr(abs(lhs - rhs), 8)})
    for p in (4, 5):
        lhs = mp.im(one_two_quadrature(0, p - 1, mp.j))
        rhs = gaussian_height_rhs(p)
        explicit.append({"row": f"gaussian_H{p}",
                         "lhs": mp.nstr(lhs, digits),
                         "rhs": mp.nstr(rhs, digits),
                         "residual": mp.nstr(abs(lhs - rhs), 8)})
    return {"working_decimal_digits": digits,
            "status": "Numerical cross-checks; proofs are in the accompanying article.",
            "records": records, "explicit_rows": explicit}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--digits", type=int, default=100)
    parser.add_argument("--output", type=Path, default=
        Path(__file__).resolve().parents[3]/"results"/"independent"/"one_two"/"verification.json")
    args = parser.parse_args()
    if args.digits < 30:
        parser.error("at least 30 working decimal digits are required")
    result = run_verification(args.digits)
    max_quad = max(mp.mpf(row["quadrature_residual"]) for row in result["records"])
    max_series = max(mp.mpf(row.get("series_residual", "0"))
                     for row in result["records"])
    max_explicit = max(mp.mpf(row["residual"]) for row in result["explicit_rows"])
    threshold=mp.power(10,-args.digits+4)
    assert max_quad < threshold
    assert max_series < threshold
    assert max_explicit < threshold
    args.output.parent.mkdir(parents=True,exist_ok=True)
    with args.output.open("w", encoding="utf-8") as stream:
        json.dump(result, stream, indent=2)
        stream.write("\n")
    print(json.dumps({"quadrature_comparisons": len(result["records"]),
                      "maximum_quadrature_residual": str(max_quad),
                      "maximum_series_residual": str(max_series),
                      "maximum_explicit_residual": str(max_explicit)}, indent=2))
