"""Exact finite reference for the manuscript's weighted-series contract.

Only finite rational arrays are computed.  The audit checks sample identities
and bounds; it is not an iPRA proof checker and does not prove universal claims.
Run with Python 3.10+: python3 code/series_contract.py --output validation/series.json
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction as Q
from pathlib import Path


def add(p, q, K):
    return [p[k] + q[k] for k in range(K + 1)]


def sub(p, q, K):
    return [p[k] - q[k] for k in range(K + 1)]


def mul(p, q, K):
    return [sum((p[i] * q[k-i] for i in range(k+1)), Q(0))
            for k in range(K + 1)]


def power(p, n, K):
    result = [Q(1)] + [Q(0)] * K
    for _ in range(n):
        result = mul(result, p, K)
    return result


def norm(p, R):
    return sum((abs(c) * R**k for k, c in enumerate(p)), Q(0))


def apply(F, p, K):
    """F is a finite list of (X-degree, Z-degree, rational coefficient)."""
    result = [Q(0)] * (K + 1)
    for i, j, coefficient in F:
        z_power = power(p, j, K)
        for k in range(i, K + 1):
            result[k] += coefficient * z_power[k-i]
    return result


def picard(F, K, count):
    stages = [[Q(0)] * (K + 1)]
    for _ in range(count):
        stages.append(apply(F, stages[-1], K))
    return stages


def certificate(F, R, rho):
    A0 = sum((abs(c) * R**i for i, j, c in F if j == 0), Q(0))
    L = sum((j * abs(c) * R**i * rho**(j-1)
             for i, j, c in F if j > 0), Q(0))
    return {
        "accepted": bool(0 < R <= 1 and 0 < rho <= 1 and A0 <= rho/2 and L <= Q(1, 2)),
        "constant_bound": A0,
        "contraction_bound": L,
    }


def evaluate(p, x):
    result = Q(0)
    for c in reversed(p):
        result = result * x + c
    return result


def clip(q, u):
    """Scalar version of the rational projection onto the norm ball."""
    if u < 0:
        raise ValueError("negative majorant")
    return max(-u, min(u, q))


def audit():
    counts = {"accepted_certificates": 0, "invariant_checks": 0,
              "picard_distance_checks": 0, "coefficient_distance_checks": 0,
              "contraction_checks": 0, "finite_tail_checks": 0,
              "clipping_checks": 0, "rejected_certificates": 0}
    R, rho = Q(1, 8), Q(1, 4)
    # These cases have a nonzero constant defect, so coefficients do not
    # stabilize.  The distance bounds are the essential property.
    for numerator in range(-8, 9):
        alpha = Q(numerator, 128)
        F = [(0, 0, alpha/2), (1, 0, Q(1, 2)), (0, 2, Q(-1, 2))]
        cert = certificate(F, R, rho)
        assert cert["accepted"]
        counts["accepted_certificates"] += 1
        K = 5
        stages = picard(F, K, 6)
        for n, p in enumerate(stages):
            assert norm(p, R) <= rho
            counts["invariant_checks"] += 1
            for m in range(n, len(stages)):
                difference = sub(stages[m], p, K)
                assert norm(difference, R) <= rho * Q(1, 2)**n
                counts["picard_distance_checks"] += 1
                for k, coefficient in enumerate(difference):
                    assert abs(coefficient) <= rho * R**(-k) * Q(1, 2)**n
                    counts["coefficient_distance_checks"] += 1
                image_difference = sub(apply(F, stages[m], K), apply(F, p, K), K)
                assert norm(image_difference, R) <= norm(difference, R)/2
                counts["contraction_checks"] += 1

    # Zero-constant specialization: the first K coefficients stabilize,
    # giving an exact finite sample of the limiting series.
    F0 = [(1, 0, Q(1, 2)), (0, 2, Q(-1, 2))]
    coefficient_bound = picard(F0, 12, 12)[-1]
    assert coefficient_bound[:5] == [Q(0), Q(1, 2), Q(-1, 8), Q(1, 16), Q(-5, 128)]
    assert norm(coefficient_bound, R) <= rho
    for k in range(9):
        for x in [Q(-1, 16), Q(-1, 32), Q(0), Q(1, 32), Q(1, 16)]:
            for m in range(k+1, 13):
                tail = sum((coefficient_bound[j] * x**j for j in range(k+1, m+1)), Q(0))
                assert abs(tail) <= rho * Q(1, 2)**(k+1)
                counts["finite_tail_checks"] += 1

    # Exact finite check of the projection fact used to reduce Cauchy-name
    # calculations to coefficient-majorized rational calculations.
    for u in [Q(0), Q(1, 8), Q(1), Q(3)]:
        for f in [-u, -u/2, Q(0), u/2, u]:
            for e in [Q(-1), Q(-1, 16), Q(0), Q(1, 16), Q(1)]:
                q = f + e
                assert abs(clip(q, u)) <= u
                assert abs(clip(q, u)-f) <= 2 * abs(e)
                counts["clipping_checks"] += 1

    invalid = [([(0, 0, Q(1))], R, rho),
               ([(0, 1, Q(1))], R, rho),
               (F0, Q(0), rho), (F0, R, Q(0))]
    for F, r, radius in invalid:
        assert not certificate(F, r, radius)["accepted"]
        counts["rejected_certificates"] += 1

    return {
        "status": "passed",
        "scope": "Exact finite reference checks only; not an iPRA proof checker.",
        "arithmetic": "Python fractions.Fraction; no floating-point comparisons",
        "certificate_example": {"R": "1/8", "rho": "1/4", "alpha_bound": "1/16",
                                "A0_bound": "3/32", "Q_bound": "1/4"},
        "counts": counts,
        "total_checks": sum(counts.values()),
        "zero_constant_coefficients_0_to_4": [str(x) for x in coefficient_bound[:5]],
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = audit()
    rendered = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered)
    print(rendered, end="")
