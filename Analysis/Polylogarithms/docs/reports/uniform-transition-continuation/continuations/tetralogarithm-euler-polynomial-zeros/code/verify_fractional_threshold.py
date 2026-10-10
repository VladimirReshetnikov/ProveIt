#!/usr/bin/env python3
"""Exact two-sign certificate for the half-order comparison threshold.

Dependency: verify_fractional.py must be in this script's directory. This
replay deliberately reuses that exact square-root interval / finite Euler
sum engine. It is not claimed to be an independent arithmetic engine.

The article proves unique crossing for the continuous truncation-order
interpolation. Combined with this file's signs at N=20 and N=21, it follows
that the integer ordering reverses exactly at N=21.
"""

from __future__ import annotations

import argparse
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import verify_fractional as engine


def sign_certificate(N: int) -> dict:
    M = N + 100
    bits = N + 200
    half, axis = engine.coefficients(M, bits)
    interval = engine.add_interval(
        engine.add_interval(engine.euler(N, half),
                            engine.scale_interval(-1, engine.euler(M, half))),
        engine.add_interval(engine.scale_interval(-1, engine.euler(N, axis)),
                            engine.euler(M, axis)),
    )
    interval = engine.scale_interval(F(1 << N), interval)

    # Both scaled tails lie in (0, 57/50), so their difference has
    # magnitude <57/50. One radius, rather than twice that radius, suffices.
    tail_radius = F(57, 50) * F(1, 1 << (M - N))
    interval = interval[0] - tail_radius, interval[1] + tail_radius
    sign = 1 if interval[0] > 0 else -1 if interval[1] < 0 else 0
    expected = -1 if N == 20 else 1
    assert sign == expected, (N, interval)
    return {
        "N": N,
        "M": M,
        "dyadic_precision_bits": bits,
        "difference": "R_N(1/2,1/2) - R_N(0,1)",
        "tail_radius": [tail_radius.numerator, tail_radius.denominator],
        "lower": [interval[0].numerator, interval[0].denominator],
        "upper": [interval[1].numerator, interval[1].denominator],
        "decimal_enclosure": engine.exact_decimal_enclosure(interval, 24),
        "certified_sign": sign,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("fractional_threshold_certificate.json"))
    args = parser.parse_args()
    engine_path = Path(engine.__file__).resolve()
    rows = [sign_certificate(N) for N in (20, 21)]
    result = {
        "status": "PASS",
        "arithmetic": "exact fractions and integer-square-root bounds",
        "dependency": {
            "filename": engine_path.name,
            "sha256": hashlib.sha256(engine_path.read_bytes()).hexdigest(),
            "role": "reused exact interval and Euler-sum engine; not an independent implementation",
        },
        "analytic_inputs": [
            "Uniform scaled Euler tails satisfy 0 < R_M(a,b) < 57/50.",
            "The article proves a unique continuous truncation-order crossing for 0<a<1,b>0.",
        ],
        "finite_certificate_scope": "The two displayed signs only; the all-N classification uses the article's theorem.",
        "theorem_dependent_conclusion": {
            "continuous_threshold_interval": [20, 21],
            "negative_integer_orders": "1 <= N <= 20",
            "positive_integer_orders": "N >= 21",
            "first_positive_integer_order": 21,
        },
        "rows": rows,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": result["status"],
                      "rows": [{"N": row["N"],
                                "decimal_enclosure": row["decimal_enclosure"],
                                "certified_sign": row["certified_sign"]}
                               for row in rows]}, indent=2))


if __name__ == "__main__":
    main()
