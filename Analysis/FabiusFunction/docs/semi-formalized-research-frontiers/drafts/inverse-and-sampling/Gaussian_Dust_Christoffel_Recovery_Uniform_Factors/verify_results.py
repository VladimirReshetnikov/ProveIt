#!/usr/bin/env python3
"""Exact algebraic checks and explicitly non-rigorous Fourier diagnostics.

Run from any working directory. This program never accesses the network.
It does not verify the universal analytic/statistical theorems or run Lean.
"""
from __future__ import annotations

import csv
import json
import platform
from pathlib import Path
from random import Random
from typing import Sequence

import mpmath as mp
import sympy as sp

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "artifacts"
OUT.mkdir(exist_ok=True)
R = sp.Rational
COUNTS: dict[str, int] = {}


def require(condition: bool, category: str, detail: str) -> None:
    """Use explicit exceptions so Python -O cannot disable validation."""
    if not bool(condition):
        raise AssertionError(f"{category}: {detail}")
    COUNTS[category] = COUNTS.get(category, 0) + 1


def power(xs: Sequence[sp.Rational], k: int) -> sp.Expr:
    return sum((x**k for x in xs), sp.S.Zero)


def finite_certificate(xs: Sequence[sp.Rational], s: sp.Rational, d: int) -> sp.Expr:
    v = s + power(xs, 1) / 3
    if d == 0:
        return v
    h = sp.Matrix(d, d, lambda i, j: power(xs, i + j + 3))
    y = sp.Matrix([power(xs, i + 2) for i in range(d)])
    return sp.factor(v - (y.T * h.pinv() * y)[0] / 3)


def check_cumulants() -> None:
    t = sp.Symbol("t")
    series = sp.series(sp.log(sp.sinh(t) / t), t, 0, 18).removeO().expand()
    values = []
    for k in range(1, 9):
        got = sp.factor(series.coeff(t, 2 * k) * sp.factorial(2 * k))
        expected = 2**(2 * k) * sp.bernoulli(2 * k) / (2 * k)
        require(got == expected, "cumulants", f"order {2*k}")
        values.append({"order": 2*k, "value": str(got)})
    (OUT / "cumulants.json").write_text(json.dumps(values, indent=2) + "\n")
    require((R(1, 5) + R(1, 3)) / sp.factorial(4) == R(1, 45),
            "dust_constants", "fourth-order absolute remainder")
    require((R(1, 5) - R(1, 3)) / sp.factorial(4) == -R(1, 180),
            "dust_constants", "signed fourth-order coefficient")
    require((R(1, 7) + R(5, 9)) / sp.factorial(6) == R(11, 11340),
            "dust_constants", "sixth-order absolute remainder")
    require(R(11, 11340) + R(1, 1080) == R(43, 22680),
            "dust_constants", "combined sixth-derivative coefficient")
    require(R(1, 2 * 45**2) == R(1, 4050),
            "dust_constants", "double telescoping coefficient")
    require(R(9, 360) == R(1, 40),
            "dust_constants", "equal-dust TV coefficient")


def check_geometric() -> None:
    rows = []
    for C in (R(1, 4), R(1), R(3, 2)):
        for r in (R(1, 4), R(1, 2), R(2, 3), R(3, 5)):
            for d in range(9):
                m = sp.Matrix(d + 1, d + 1,
                              lambda i, j: C**(i+j+1)/(1-r**(i+j+1)))
                if d:
                    h, y = m[1:, 1:], m[1:, 0]
                    actual = sp.factor(m[0, 0] - (y.T * h.inv() * y)[0])
                else:
                    actual = m[0, 0]
                predicted = C * (1-r) * r**d / (1-r**(d+1))**2
                require(actual == predicted, "geometric_schur", f"C={C},r={r},d={d}")
                if d <= 5:
                    detratio = m.det() / (m[1:, 1:].det() if d else 1)
                    require(detratio == predicted, "geometric_determinants",
                            f"C={C},r={r},d={d}")
                require(0 < actual <= C*r**d/(1-r), "geometric_tail",
                        f"C={C},r={r},d={d}")
                rows.append({"C": str(C), "r": str(r), "degree": d,
                             "bias": str(predicted/3)})
    with (OUT / "geometric_checks.csv").open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=rows[0].keys())
        w.writeheader(); w.writerows(rows)
    with (OUT / "dyadic_bias.csv").open("w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["degree", "highest_cumulant_order", "exact_bias", "decimal_bias"])
        for d in range(13):
            bias = R(1, 4)**d / (16*(1-R(1, 4)**(d+1))**2)
            w.writerow([d, 4*d+2, str(bias), str(sp.N(bias, 25))])


def check_finite_and_noise() -> None:
    rng = Random(20260929)
    L = R(12)
    for trial in range(128):
        xs = sorted((R(rng.randrange(0, 9), 16)
                     for _ in range(rng.randrange(0, 9))), reverse=True)
        s = R(rng.randrange(0, 9), 16)
        v = s + power(xs, 1)/3
        require(3*v <= L, "finite_budget", str(trial))
        last = v
        for m in range(10):
            value = v - sum(((-1)**(r+1)*sp.binomial(m, r)*power(xs, r+1)/L**r
                             for r in range(1, m+1)), sp.S.Zero)/3
            bias = sum((x*(1-x/L)**m for x in xs), sp.S.Zero)/3
            require(value-s == bias, "ladder_identity", f"trial={trial},m={m}")
            require(s <= value <= last, "ladder_monotonicity", f"trial={trial},m={m}")
            if m:
                require(power(xs[2*m:], 1) <= 6*bias, "ladder_converse",
                        f"trial={trial},m={m}")
            last = value
        if trial < 16:
            last = v
            distinct = len(set(x for x in xs if x > 0))
            for d in range(5):
                c = finite_certificate(xs, s, d)
                require(s <= c <= last, "finite_christoffel_monotonicity",
                        f"trial={trial},d={d}")
                require(c-s <= power(xs[d:], 1)/3, "finite_christoffel_tail",
                        f"trial={trial},d={d}")
                require((c == s) == (distinct <= d), "finite_exact_termination",
                        f"trial={trial},d={d}")
                last = c
        d = rng.randrange(1, 6)
        coeff = [R(1)] + [R(rng.randrange(-4, 5), 8) for _ in range(d)]
        norm = sum(abs(c) for c in coeff)
        eps = R(1, 10**5)
        moments = [3*v] + [power(xs, r+1)/L**r for r in range(1, 2*d+1)]
        errors = [eps * ((r % 3)-1) for r in range(2*d+1)]
        diff = sum(coeff[i]*coeff[j]*errors[i+j]
                   for i in range(d+1) for j in range(d+1))
        require(abs(diff) <= eps*norm**2, "coefficient_noise", f"trial={trial}")
        positive = [x for x in xs if x > 0]
        if positive:
            z = sp.Symbol("z")
            product = sp.Poly(sp.prod(1-L*z/x for x in positive[:d]), z)
            l1 = sum(abs(c) for c in product.all_coeffs())
            predicted = sp.prod(1+L/x for x in positive[:d])
            require(l1 == predicted, "annihilator_coefficient_norm", f"trial={trial}")


def fourier_diagnostic() -> None:
    mp.mp.dps = 90
    rows = []
    for frequency in (mp.mpf(1)/3, mp.mpf(1), mp.mpf(2)):
        target = -frequency**4/20
        for n in (4, 16, 64, 256, 1024, 4096, 16384):
            z = mp.sqrt(mp.mpf(3)/n)*frequency
            log_ratio = n*mp.log(mp.sin(z)/z) + frequency**2/2
            scaled = n*mp.expm1(log_ratio)
            rows.append({"frequency": mp.nstr(frequency, 24), "factors": n,
                         "scaled_characteristic_ratio": mp.nstr(scaled, 40),
                         "predicted_limit": mp.nstr(target, 40),
                         "absolute_error": mp.nstr(abs(scaled-target), 30)})
        require(abs(scaled-target) < mp.mpf("0.001"), "fourier_diagnostic",
                f"frequency={frequency}; diagnostic, not an interval certificate")
    with (OUT / "fourier_diagnostic.csv").open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=rows[0].keys())
        w.writeheader(); w.writerows(rows)


def main() -> None:
    check_cumulants()
    check_geometric()
    check_finite_and_noise()
    fourier_diagnostic()
    result = {
        "status": "all checks passed",
        "checks_by_category": COUNTS,
        "total_checks": sum(COUNTS.values()),
        "exact_checks": sum(v for k, v in COUNTS.items() if k != "fourier_diagnostic"),
        "high_precision_diagnostics": COUNTS.get("fourier_diagnostic", 0),
        "seed": 20260929,
        "software": {"python": platform.python_version(), "sympy": sp.__version__,
                     "mpmath": mp.__version__},
        "limitations": ["Finite checks are not proofs of universal theorems.",
                        "Fourier diagnostics do not compute total variation.",
                        "No interval arithmetic, independent referee review, or Lean verification."]}
    (OUT / "verification_results.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
