#!/usr/bin/env python3
"""Reproduce the exact and numerical checks in article.tex.

All coefficient rows and moment unit tests use exact integers/rationals.
Only normalized errors and inverse evaluations use mpmath floating point.
These are finite checks, not proofs of the asymptotic error estimates.
"""
from __future__ import annotations

import argparse
import csv
import math
from fractions import Fraction
from pathlib import Path
import time
from typing import Sequence

import mpmath as mp

FIRST_TWENTY = (
    1, 2, 4, 13, 57, 315, 2057, 15484, 132317, 1261560,
    13281295, 153218597, 1921565205, 26008169266, 377922606876,
    5871153031163, 97096594212804, 1702487540383101,
    31551431772637772, 616331122530164638,
)


def next_row(previous: Sequence[int], n: int) -> list[int]:
    """Multiply the row for P_(n-1) by 1 + q + q^3 + ... + q^(2n-1)."""
    if n < 1 or len(previous) != (n - 1) ** 2 + 1:
        raise ValueError("The previous row must have (n-1)^2+1 entries.")
    result = [0] * (n * n + 1)
    running = [0, 0]
    length = len(previous)
    for k in range(len(result)):
        if 0 <= k - 1 < length:
            running[k % 2] += previous[k - 1]
        if 0 <= k - 2 * n - 1 < length:
            running[k % 2] -= previous[k - 2 * n - 1]
        result[k] = running[k % 2] + (previous[k] if k < length else 0)
    return result


def naive_next_row(previous: Sequence[int], n: int) -> list[int]:
    """Independent, deliberately slow direct convolution for unit testing."""
    result = [0] * (len(previous) + 2 * n - 1)
    for k, value in enumerate(previous):
        result[k] += value
        for a in range(1, n + 1):
            result[k + 2 * a - 1] += value
    return result


def harmonic(n: int, order: int = 1) -> Fraction:
    return sum((Fraction(1, j ** order) for j in range(1, n + 1)), Fraction())


def exact_cumulants(row: Sequence[int]) -> tuple[Fraction, Fraction, Fraction]:
    """First three cumulants; also valid for nonzero-mass signed rows."""
    mass = sum(row)
    if mass == 0:
        raise ValueError("Cannot normalize a zero-mass row.")
    m1, m2, m3 = (
        Fraction(sum(value * k ** r for k, value in enumerate(row)), mass)
        for r in (1, 2, 3)
    )
    return m1, m2 - m1 ** 2, m3 - 3 * m2 * m1 + 2 * m1 ** 3


def unit_tests() -> None:
    row = [1]
    for n in range(1, 11):
        fast, slow = next_row(row, n), naive_next_row(row, n)
        assert fast == slow, f"Convolution disagreement at n={n}"
        row = fast
        h, h2, h3 = (harmonic(n + 1, r) for r in (1, 2, 3))
        expected = (
            Fraction(n * (n - 1), 2) + h - 1,
            Fraction(n ** 3, 9) + Fraction(n ** 2, 2)
            - Fraction(29 * n, 18) + 3 * h - h2 - 2,
            n ** 2 - 6 * n + 14 * h - 9 * h2 + 2 * h3 - 7,
        )
        assert exact_cumulants(row) == expected, f"Moment disagreement n={n}"
        assert sum(row[::2]) == sum(row[1::2]), f"Parity mass disagreement n={n}"
        assert sum(row) == math.factorial(n + 1)
        assert max(row) == FIRST_TWENTY[n - 1]

    # Check the signed-factor formulas used to build B_n.
    for j in range(2, 20):
        signed_row = [-1] + [1 if k % 2 else 0 for k in range(1, 2 * j)]
        b1, b2, b3 = exact_cumulants(signed_row)
        assert b1 == Fraction(j * j, j - 1)
        assert b2 == (Fraction(j * j, 3) - Fraction(2 * j, 3) - 2
                      - Fraction(3, j - 1) - Fraction(1, (j - 1) ** 2))
        assert b3 == (2 * j + 7 + Fraction(14, j - 1)
                      + Fraction(9, (j - 1) ** 2) + Fraction(2, (j - 1) ** 3))

    for n in range(2, 15):
        means = Fraction(1, 2)  # (exp(t)-1)/t, uniform[0,1]
        variances = Fraction(1, 12)
        for j in range(2, n + 1):
            signed_row = [-1] + [1 if k % 2 else 0 for k in range(1, 2 * j)]
            b1, b2, _ = exact_cumulants(signed_row)
            means += b1
            variances += b2
        assert means == (Fraction(n * (n + 3), 2) - Fraction(3, 2)
                         + harmonic(n - 1))
        assert variances == (Fraction(n ** 3, 9) - Fraction(n ** 2, 6)
                             - Fraction(41 * n, 18) + Fraction(29, 12)
                             - 3 * harmonic(n - 1) - harmonic(n - 1, 2))
    print("PASS: independent small-row convolution, exact cumulants, "
          "parity masses, and signed-neighborhood formulas.")


def write_csv(path: Path, header: Sequence[str], rows: Sequence[Sequence[object]]) -> None:
    with path.open("w", newline="", encoding="utf-8") as output:
        writer = csv.writer(output)
        writer.writerow(header)
        writer.writerows(rows)


def run(max_n: int, digits: int, output_dir: Path) -> None:
    if max_n < 1 or digits < 40:
        raise ValueError("Require max_n >= 1 and digits >= 40.")
    mp.mp.dps = digits
    output_dir.mkdir(parents=True, exist_ok=True)
    unit_tests()
    start = time.monotonic()
    row = [1]
    data: list[list[object]] = []
    inverse_data: list[list[object]] = []
    failures: list[int] = []
    threshold_failures: list[int] = []
    c1 = -mp.mpf(431) / 300
    c2 = mp.mpf(23085971) / 1764000
    const3 = mp.mpf(107751433393) / 1587600000
    const4 = mp.mpf(155775441709528423) / 322727328000000
    q = mp.mpf(1263) / 40
    h = mp.mpf(1)
    h2 = mp.mpf(1)
    checkpoints = {10, 20, 50, 100, 200, 300, 400, max_n}
    for n in range(1, max_n + 1):
        row = next_row(row, n)
        h += mp.mpf(1) / (n + 1)
        h2 += mp.mpf(1) / (n + 1) ** 2
        value = max(row)
        modes = [k for k, coefficient in enumerate(row) if coefficient == value]
        assert sum(row) == math.factorial(n + 1), f"Mass failure at n={n}"
        assert sum(row[::2]) == sum(row[1::2]), f"Parity failure at n={n}"
        if n <= 20:
            assert value == FIRST_TWENTY[n - 1], f"OEIS mismatch at n={n}"
        mu = mp.mpf(n * (n - 1)) / 2 + h - 1
        k = modes[0]
        d = k - mu
        c3 = -mp.mpf(9) / 2 * d ** 2 - mp.mpf(27) / 2 * h + mp.mpf(9) / 2 * h2 - const3
        c4 = q * d ** 2 - mp.mpf(81) / 2 * d + 3 * q * h - q * h2 + const4 - 18 * (-1) ** (n + k)
        scale = 3 * mp.exp(n * mp.log(n) - n)
        ratio = mp.mpf(value) / scale
        approximations = [
            mp.mpf(1), 1 + c1 / n, 1 + c1 / n + c2 / n ** 2,
            1 + c1 / n + c2 / n ** 2 + c3 / n ** 3,
            1 + c1 / n + c2 / n ** 2 + c3 / n ** 3 + c4 / n ** 4,
        ]
        errors = [(a - ratio) / ratio for a in approximations]
        lower = int(mp.floor(mu))
        r = mu - lower - mp.mpf("0.5")
        sign = (-1) ** (n + lower)
        boundary = (mp.mpf("4.5") - 4 * sign) / n
        prediction = lower + int(r > boundary)
        single_peak = int(mp.floor(mu - mp.mpf("4.5") / n + mp.mpf("0.5")))
        if n >= 50 and single_peak not in modes:
            failures.append(n)
        if n >= 50 and prediction not in modes:
            threshold_failures.append(n)
        difference = (mp.mpf(row[lower + 1]) - row[lower]) / scale
        d0 = lower - mu
        difference_approx = -9 * (d0 + mp.mpf("0.5")) / n ** 3
        difference_approx += (q * (2 * d0 + 1) - mp.mpf("40.5") + 36 * sign) / n ** 4
        residual = (difference - difference_approx) * n ** 5
        data.append([
            n, str(value), ",".join(map(str, modes)), mp.nstr(mu, 35),
            mp.nstr(d, 25), mp.nstr(ratio, 30),
            *[mp.nstr(e, 15) for e in errors], prediction, mp.nstr(residual, 15),
        ])
        if n in checkpoints:
            print(f"n={n:4d}; modes={modes}; "
                  f"normalized maximum={mp.nstr(ratio, 13)}; "
                  f"order-4 relative error={mp.nstr(errors[4], 9)}", flush=True)
        if n in {50, 100, 200, 400}:
            ell = mp.log(mp.mpf(value) / 3)
            x = ell / mp.lambertw(ell / mp.e)
            corrected = (x + mp.mpf(431) / (300 * x * mp.log(x))
                         - mp.mpf(5907087) / (490000 * x ** 2 * mp.log(x)))
            inverse_data.append([n, mp.nstr(x - n, 30), mp.nstr(corrected - n, 30)])
    write_csv(output_dir / "numerical_results.csv", [
        "n", "maximum", "modes", "mean", "mode_minus_mean", "normalized_maximum",
        "relerr_leading", "relerr_1", "relerr_2", "relerr_3", "relerr_4",
        "mode_prediction", "adjacent_scaled_remainder",
    ], data)
    write_csv(output_dir / "inverse_results.csv", [
        "n", "lambert_core_minus_n", "two_correction_inverse_minus_n",
    ], inverse_data)
    print(f"PASS: exact rows through n={max_n}; masses and first OEIS values verified.")
    print("Single-peak rounding failures with n>=50:", failures)
    print("Unqualified first-order parity-rule failures with n>=50:", threshold_failures)
    print("The latter rule has an asymptotic boundary-layer error; "
          "its small-n failures are not contradictions.")
    print(f"Numerical precision: {digits} decimal digits; "
          f"elapsed: {time.monotonic() - start:.2f} seconds.")
    print("Floating-point errors in the CSVs are not certified intervals.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, default=400)
    parser.add_argument("--digits", type=int, default=70)
    parser.add_argument("--out", type=Path, default=Path(__file__).resolve().parent / "data")
    args = parser.parse_args()
    run(args.max_n, args.digits, args.out)
