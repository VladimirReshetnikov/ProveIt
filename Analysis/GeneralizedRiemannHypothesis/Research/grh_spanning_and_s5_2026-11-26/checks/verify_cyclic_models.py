#!/usr/bin/env python3
"""Exact arithmetic checks for the spanning theorems in report.tex.

No third-party packages, floating point, or network are used. These are
instantiations and checks, not a replacement for the mathematical proof.
The finite cyclic examples are genuine complex linear maps with orthogonal
coordinate images and optional source kernels. Squared lengths are rational,
so all moment and dimension checks take place in fractions.Fraction.
"""

from fractions import Fraction as F
from math import ceil, floor
import argparse
import json
from pathlib import Path
from random import Random


def frac(x):
    return str(x.numerator) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"


def shift(support, g, r):
    return {(x + g) % r for x in support}


def check_model(d, r, s, k, u, v, support):
    """G=C_r rotates r coordinates and fixes d-r dormant coordinates.

    B has m=s-k orthogonal nonzero columns of squared length c2, and k
    zero columns. Since I-B*B is positive semidefinite with trace u*s,
    tr(P_U(I-B*B)) <= u*s for every U: the near-isometry hypothesis holds.
    The group second moment is independently summed through overlaps.
    """
    a, z = 1 - u, 1 + v
    m = s - k
    assert 0 < m <= r <= d and len(support) == m
    c2 = a * s / m
    assert 0 < c2 <= 1
    deficit_eigenvalues = [F(1)] * k + [1 - c2] * m
    assert sum(deficit_eigenvalues) == u * s
    assert min(deficit_eigenvalues) >= 0

    overlaps = [len(support & shift(support, g, r)) for g in range(r)]
    second_moment = sum(c2 * c2 * j for j in overlaps) / r
    assert sum(overlaps) == m * m
    assert d * second_moment <= z * s * s

    alpha = a * a / z
    delta = 1 - alpha
    h = F(s, 2 * d) * z / a
    q = max(F(0), 1 - h)
    assert 0 <= q < 1
    assert F(s, d) <= 1 / a

    current = set()
    selected = set()
    # Remove up to two ACTIVE source columns, retaining every kernel column.
    removed = min(2, m)
    retained_support = set(sorted(support)[removed:])
    restricted = set()
    checks = 0
    for t in range(r + 2):
        upper = d * (delta + alpha * q**t)
        assert d - len(current) <= upper
        assert d - len(restricted) <= upper + t * removed
        assert len(selected) <= t
        checks += 2
        if len(current) == r:
            assert d - r <= d * delta
            break

        g = max(range(r), key=lambda j: len(shift(support, j, r) - current))
        image = shift(support, g, r)
        gain = len(image - current)
        preimage_dim = s - gain
        rhs_square_root_argument = z * F(len(current), d)
        lhs = F(preimage_dim, s) - u
        # Equivalent to the square-root estimate whenever lhs is positive.
        if lhs > 0:
            assert lhs * lhs <= rhs_square_root_argument
        checks += 1
        assert gain > 0
        selected.add(g)
        current.update(image)
        restricted.update(shift(retained_support, g, r))
    else:
        raise AssertionError("Greedy process did not reach the cyclic support")
    return checks, q == 0


def run():
    rng = Random(26735)
    pairs = [
        (F(0), F(0)),
        (F(1, 10), F(1, 3)),
        (F(1, 4), F(1, 5)),
        (F(1, 2), F(1, 2)),
        (F(9, 10), F(0)),
        (F(5, 256), F(9, 256)),
    ]
    models = checks = kernels = zero_q = 0
    for u, v in pairs:
        a, z = 1 - u, 1 + v
        alpha = a * a / z
        for d in range(1, 25):
            r = ceil(d * alpha)
            smax = floor(F(r) / a)
            for s in sorted({1, r, max(1, smax // 2), smax}):
                if s > smax:
                    continue
                for k in sorted({max(0, s - r), floor(u * s)}):
                    m = s - k
                    if not (0 < m <= r and k <= u * s):
                        continue
                    support = set(rng.sample(range(r), m))
                    nchecks, is_zero_q = check_model(d, r, s, k, u, v, support)
                    checks += nchecks
                    models += 1
                    kernels += int(k > 0)
                    zero_q += int(is_zero_q)

    sharp_examples = []
    for b in [2, 3, 4, 6, 10, 25]:
        Q = b**4
        u, v = F(5, Q), F(9, Q)
        d, r = Q * (Q + 9), (Q - 5) ** 2
        alpha = (1 - u) ** 2 / (1 + v)
        moment = (1 - u) ** 2 / r
        assert F(r, d) == alpha
        assert d * moment == 1 + v
        assert d - r == 19 * Q - 25
        assert F(d - r, d) == F(19, Q) - F(196, Q * (Q + 9))
        # For two smaller models explicitly enumerate every cyclic group element.
        enumerated = b in (2, 3)
        if enumerated:
            values = [(1 - u) ** 2 if g == 0 else F(0) for g in range(r)]
            assert sum(values) / r == moment
        sharp_examples.append({
            "b": b, "ambient_dimension": d, "orbit_rank": r,
            "missing_dimensions": d-r, "missing_share": frac(F(d-r, d)),
            "near_isometry_error": frac(u), "moment_excess": frac(v),
            "all_group_elements_enumerated": enumerated,
        })

    for b in range(6, 201):
        u, v = F(5, b**4), F(9, b**4)
        a, z = 1 - u, 1 + v
        assert z / (2 * a * a) < 1
        assert (2 * u + v - u * u) / (1 + v) <= F(19, b**4)
        assert F(19) + F(3, 4) + F(8, b*b) < 20
    for b in range(4, 201):
        assert F(19) + F(1, b) + F(10, b*b) < 20

    assert F(19) + F(3, 4) + F(8, 36) == F(719, 36)
    assert F(19) + F(1, 4) + F(10, 16) == F(159, 8)
    return {
        "status": "all exact-arithmetic checks passed",
        "source_commit": "72fead102f663d5c7a407964a13dc0cf9d977207",
        "cyclic_models_checked": models,
        "models_with_source_kernel": kernels,
        "models_with_q_zero": zero_q,
        "preimage_and_dimension_checks": checks,
        "four_budget_coarse_constant_at_b6": "719/36 < 20",
        "five_budget_coarse_constant_at_b4": "159/8 < 20",
        "sharp_raw_examples": sharp_examples,
        "scope": (
            "Exact instantiated linear-algebra and rational-constant checks; "
            "the general theorem is proved in the accompanying mathematical text. "
            "This script does not run Lean or rebuild grh-lean."
        ),
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = run()
    text = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(text)
    print(text, end="")
