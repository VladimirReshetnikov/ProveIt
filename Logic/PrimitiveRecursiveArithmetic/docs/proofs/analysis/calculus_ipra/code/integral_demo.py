#!/usr/bin/env python3
"""Exact rational finite checks for the integral-name construction.

This evaluates f(x)=1/(1+x) on [0,1], with the strictly increasing
continuity modulus mu(k)=k and bound M=1.  All finite comparisons are
Fraction comparisons.  These checks do not prove the theorem schema,
and do not claim a Lean or object-theory iPRA certificate.

Run: python3 integral_demo.py --output integral_validation.json
"""

from __future__ import annotations

import argparse
import json
from decimal import Decimal, localcontext
from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path


def epsilon(k: int) -> Q:
    if k < 0:
        raise ValueError("precision must be nonnegative")
    return Q(1, 2**k)


def sigma(z: Q | int) -> int:
    """Bounded-search version of the paper's dyadic scale selector."""
    z = max(Q(1), Q(z))
    ceiling = (z.numerator + z.denominator - 1) // z.denominator
    for n in range(ceiling + 2):
        if 2**n >= z:
            return n
    raise AssertionError("the proved elementary bound was violated")


def value(x: Q, precision: int) -> Q:
    """Exact rational evaluation; coherence error is actually zero."""
    if not Q(0) <= x <= Q(1):
        raise ValueError("argument is outside [0,1]")
    return 1 / (1 + x)


def modulus(k: int) -> int:
    return k


@lru_cache(maxsize=None)
def canonical(u: Q, v: Q, k: int) -> Q:
    """Equation (4.3), with one global length bound s=0 on [0,1]."""
    if u > v:
        return -canonical(v, u, k)
    if u == v:
        return Q(0)
    if not Q(0) <= u <= v <= Q(1):
        raise ValueError("interval is outside [0,1]")
    s = 0
    c = k + s + 4
    count = 2 ** (s + modulus(c))
    step = (v - u) / count
    return step * sum((value(u + i * step, c) for i in range(count)), Q(0))


def decimal_string(x: Q, digits: int = 24) -> str:
    """Display only; not used in any proof check."""
    with localcontext() as context:
        context.prec = digits
        return str(Decimal(x.numerator) / Decimal(x.denominator))


def validate() -> dict:
    intervals = [(Q(0), Q(1)), (Q(0), Q(1, 3)),
                 (Q(1, 3), Q(1)), (Q(1, 4), Q(3, 4))]
    cauchy_checks = 0
    for u, v in intervals:
        for k in range(6):
            for l in range(k, 6):
                assert abs(canonical(u, v, k) - canonical(u, v, l)) <= (
                    epsilon(k) / 8 + epsilon(l) / 16)
                cauchy_checks += 1

    additivity_checks = 0
    for split in [Q(1, 4), Q(1, 3), Q(1, 2), Q(3, 4)]:
        for p in range(5):
            defect = abs(canonical(Q(0), Q(1), p)
                         - canonical(Q(0), split, p)
                         - canonical(split, Q(1), p))
            assert defect <= epsilon(p) / 4
            additivity_checks += 1

    derivative_checks = 0
    for k in range(4):
        step = epsilon(k + 2)
        for x in [Q(1, 4), Q(1, 2), Q(3, 4)]:
            for direction in [-1, 1]:
                y = x + direction * step
                if not Q(0) <= y <= Q(1):
                    continue
                for p in range(4):
                    delta = y - x
                    defect = abs(canonical(Q(0), y, p)
                                 - canonical(Q(0), x, p)
                                 - delta * value(x, p))
                    bound = abs(delta) * epsilon(k) + (2 + abs(delta)) * epsilon(p)
                    assert defect <= bound
                    derivative_checks += 1

    # A sharper radius available for exact evaluations of a 1-Lipschitz
    # function: each left sum at mesh 1/N is within 1/N of the integral.
    # The interval is a representation of the integral; no math.log value
    # or floating-point result is used as a correctness oracle.
    examples = []
    for k in [0, 2, 4, 6]:
        count = 2 ** (k + 4)
        approximation = canonical(Q(0), Q(1), k)
        radius = Q(1, count)
        examples.append({
            "output_precision_k": k,
            "grid_cells": count,
            "display_approximation": decimal_string(approximation),
            "certified_radius_exact": str(radius),
            "display_lower_endpoint": decimal_string(approximation - radius),
            "display_upper_endpoint": decimal_string(approximation + radius),
            "radius_justification": "finite left-sum bound for 1-Lipschitz f; exact samples",
        })

    # Rational nonzero increments are divided only after a decidable check.
    assert all(sigma(Q(i, 7)) <= i + 2 for i in range(1, 40))
    return {
        "status": "passed",
        "scope": "Finite exact-rational implementation checks, not a formal proof of iPRA derivability.",
        "function": "f(x)=1/(1+x) on [0,1]",
        "modulus": "mu(k)=k (strictly increasing); |f(x)-f(y)|<=|x-y|",
        "global_length_scale_s": 0,
        "cauchy_checks": cauchy_checks,
        "additivity_checks": additivity_checks,
        "derivative_certificate_checks": derivative_checks,
        "examples": examples,
        "decimal_output": "display only; all comparisons above use exact Fraction arithmetic",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = validate()
    data = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(data, encoding="utf-8")
    else:
        print(data, end="")


if __name__ == "__main__":
    main()
