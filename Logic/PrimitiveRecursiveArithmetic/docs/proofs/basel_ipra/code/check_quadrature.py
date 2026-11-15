#!/usr/bin/env python3
"""Exact checks of the finite Riemann-sum bridge, not a universal proof."""

from __future__ import annotations
import argparse
from fractions import Fraction as Q
import json
from pathlib import Path


def gregory(n: int) -> Q:
    return sum((Q((-1)**j, 2 * j + 1) for j in range(n)), Q(0))


def riemann(m: int) -> Q:
    return sum((Q(m, m * m + i * i) for i in range(m)), Q(0))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    moments = geometric = comparisons = refinements = 0
    for p in range(33):
        for m in range(1, 49):
            moment = sum((Q(i, m)**p for i in range(m)), Q(0)) / m
            assert 0 <= Q(1, p + 1) - moment <= Q(1, m)
            moments += 1
    for n in range(1, 17):
        for m in range(1, 17):
            for i in range(m + 1):
                x = Q(i, m)
                polynomial = sum(((-1)**j * x**(2*j) for j in range(n)), Q(0))
                assert 1 / (1 + x*x) == polynomial + (-1)**n * x**(2*n) / (1+x*x)
                geometric += 1
    qs = {m: riemann(m) for m in range(1, 65)}
    for n in range(1, 25):
        a = gregory(n)
        for m in (1, 2, 3, 8, 16, 32, 64):
            assert abs(qs[m] - a) <= Q(n, m) + Q(1, 2*n+1)
            comparisons += 1
    for m in range(1, 21):
        for ell in range(1, 21):
            assert abs(qs[m]-qs[ell]) <= Q(1, 2*m) + Q(1, 2*ell)
            refinements += 1
    for k in range(256):
        assert 16*k + 124 <= 128*2**k
        assert 16*k + 92 <= 128*2**k
    report = {
        "status": "passed",
        "scope": "finite exact checks, not a universal formal proof",
        "arithmetic": "integer and Fraction; no floating-point comparisons",
        "moment_checks": moments, "geometric_identity_checks": geometric,
        "quadrature_comparisons": comparisons, "cauchy_comparisons": refinements,
        "modulus_samples_each": 256,
        "claims": [
            "0 <= 1/(p+1) - lower_power_sum(p,M) <= 1/M, including p=0",
            "finite geometric identity on rational [0,1], including both endpoints",
            "|Q_M-A_N| <= N/M + 1/(2N+1)",
            "|Q_M-Q_L| <= 1/(2M)+1/(2L)",
            "16k+124 <= 128*2^k and 16k+92 <= 128*2^k",
        ],
    }
    rendered = json.dumps(report, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered, encoding="utf-8")
    print(rendered, end="")


if __name__ == "__main__":
    main()
