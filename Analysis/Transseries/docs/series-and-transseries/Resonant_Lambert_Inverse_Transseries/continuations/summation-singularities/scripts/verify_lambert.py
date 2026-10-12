#!/usr/bin/env python3
"""Finite-coefficient diagnostics for the proved Lambert large-order expansion.

The coefficients are evaluated from the predecessor's finite Lagrange formula,
without using any asymptotic approximation in their construction. All k from 1
through n are included. The output is diagnostic numerical evidence, not an
interval certificate or a substitute for the proof.

Requires mpmath. Run, for example:
  python scripts/verify_lambert.py
"""

from __future__ import annotations

import argparse
import json
import platform
import time
from pathlib import Path

import mpmath as mp


def scaled_forward_coefficients(nmax: int) -> list[mp.mpf]:
    """Return A^n |r_n|, using the source's exact zeta coefficient formula."""
    action = 4 * mp.pi**2
    result = [mp.mpf(0)] * (nmax + 1)
    result[1] = action / 4
    for n in range(2, nmax + 1, 2):
        result[n] = 4 * mp.gamma(n) * mp.zeta(n) ** 2 / n
    return result


def all_powers(coeffs: list[mp.mpf]) -> list[list[mp.mpf]]:
    """Return all finite convolution powers of the positive absolute tail."""
    nmax = len(coeffs) - 1
    table = [[mp.mpf(0)] * (nmax + 1) for _ in range(nmax + 1)]
    table[0][0] = mp.mpf(1)
    nonzero = [j for j in range(1, nmax + 1) if coeffs[j]]
    for k in range(1, nmax + 1):
        previous = table[k - 1]
        current = table[k]
        for n in range(k, nmax + 1):
            current[n] = mp.fsum(
                previous[n - j] * coeffs[j]
                for j in nonzero
                if j <= n - k + 1
            )
    return table


def normalized_coefficient(
    n: int, u: mp.mpc, powers: list[list[mp.mpf]]
) -> mp.mpc:
    """Evaluate D_n=n A^n C_n/(4 Gamma(n)) by all finite Lagrange terms."""
    total = mp.mpc(0)
    u_power_over_factorial = mp.mpc(1)
    for k in range(1, n + 1):
        u_power_over_factorial *= u / k
        term = mp.mpc(n) ** (k - 1)
        inner = term
        for j in range(1, k):
            term *= (k - j) * (k + j - 1) * u / (2 * n * j)
            inner += term
        total += u_power_over_factorial * powers[k][n] * inner
    # Every original convolution coefficient has sign (-1)^n.
    return (-1) ** (n + 1) * total * n / (4 * mp.gamma(n))


def predictions(n: int, u: mp.mpc) -> tuple[mp.mpc, mp.mpc]:
    action = 4 * mp.pi**2
    theta = action * u / 4
    h = (1 + u) * theta**2 / 2 + u * action**2 / 288
    if n % 2 == 0:
        e = mp.cosh(theta)
        de = mp.sinh(theta)
    else:
        e = -mp.sinh(theta)
        de = -mp.cosh(theta)
    leading = -u * e
    first = -u * (h * e + (u + 2) * theta * de)
    return leading, first


def encode(z: mp.mpc) -> dict[str, str]:
    return {"real": mp.nstr(mp.re(z), 35), "imag": mp.nstr(mp.im(z), 35)}


def run(nmax: int, dps: int) -> dict:
    mp.mp.dps = dps
    start = time.perf_counter()
    coefficients = scaled_forward_coefficients(nmax)
    powers = all_powers(coefficients)
    indices = [n for n in (40, 41, 80, 81, 120, 121, 160, 161, 200, 201)
               if n <= nmax]
    parameters = [
        ("0.1", "0"),
        ("0.25", "0"),
        ("0.2", "0.1"),
        ("0", mp.nstr(1 / (2 * mp.pi), dps)),
    ]
    rows = []
    for real, imag in parameters:
        u = mp.mpc(real, imag)
        for n in indices:
            exact = normalized_coefficient(n, u, powers)
            leading, first = predictions(n, u)
            rows.append({
                "u": encode(u),
                "n": n,
                "D_n": encode(exact),
                "leading": encode(leading),
                "first_correction_coefficient": encode(first),
                "n_times_leading_error": encode(n * (exact - leading)),
                "n_squared_refined_error": encode(
                    n * n * (exact - leading - first / n)
                ),
                "absolute_leading_error": mp.nstr(abs(exact - leading), 25),
                "absolute_refined_error": mp.nstr(
                    abs(exact - leading - first / n), 25
                ),
            })
            print(
                f"u={mp.nstr(u, 9)} n={n}: "
                f"n*(D-leading)={mp.nstr(n*(exact-leading), 13)}, "
                f"predicted first={mp.nstr(first, 13)}",
                flush=True,
            )
    return {
        "description": "Full finite Lagrange coefficients versus proved large-order formulas",
        "status": "numerical diagnostics; not interval-certified",
        "source_pin": "8f5afd4d7565df808359f6a0c22f87f79a119bb9",
        "nmax": nmax,
        "decimal_precision": dps,
        "python": platform.python_version(),
        "mpmath": mp.__version__,
        "elapsed_seconds": round(time.perf_counter() - start, 3),
        "rows": rows,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--nmax", type=int, default=201)
    parser.add_argument("--dps", type=int, default=90)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1]/"results"/"lambert_checks.json")
    args = parser.parse_args()
    if args.nmax < 41 or args.dps < 40:
        parser.error("use nmax >= 41 and dps >= 40")
    result = run(args.nmax, args.dps)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {args.output}", flush=True)


if __name__ == "__main__":
    main()
