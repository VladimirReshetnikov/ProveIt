#!/usr/bin/env python3
"""Exact reference checks for the iPRA median proof packet.

All mathematical checks use integers and fractions.  The program is not a
formal proof and is not used as an oracle by the proposed Lean development; it
is executable regression evidence for the formulas in the manuscript.
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Iterable, Sequence

Q = Fraction


def q(x: int | Fraction) -> Fraction:
    return x if isinstance(x, Fraction) else Fraction(x)


def median_endpoints(xs: Sequence[int | Fraction]) -> tuple[Fraction, Fraction]:
    if not xs:
        raise ValueError("median requires a nonempty sample")
    ys = sorted(map(q, xs))
    return ys[(len(ys) - 1) // 2], ys[len(ys) // 2]


def twice_median(xs: Sequence[int | Fraction]) -> Fraction:
    lo, hi = median_endpoints(xs)
    return lo + hi


def conventional_median(xs: Sequence[int | Fraction]) -> Fraction:
    return twice_median(xs) / 2


def count_lt(xs: Sequence[int | Fraction], t: Fraction) -> int:
    return sum(q(x) < t for x in xs)


def count_gt(xs: Sequence[int | Fraction], t: Fraction) -> int:
    return sum(q(x) > t for x in xs)


def is_balance_median(xs: Sequence[int | Fraction], t: Fraction) -> bool:
    n = len(xs)
    return n > 0 and 2 * count_lt(xs, t) <= n and 2 * count_gt(xs, t) <= n


def l1_objective(xs: Sequence[int | Fraction], t: Fraction) -> Fraction:
    return sum((abs(q(x) - t) for x in xs), Q(0))


def support_weights(items: Iterable[tuple[int | Fraction, int]]) -> list[tuple[Fraction, int]]:
    c: Counter[Fraction] = Counter()
    for x, w in items:
        if w < 0:
            raise ValueError("negative weight")
        c[q(x)] += w
    return [(x, c[x]) for x in sorted(c) if c[x] > 0]


def weighted_median_endpoints(items: Iterable[tuple[int | Fraction, int]]) -> tuple[Fraction, Fraction]:
    sw = support_weights(items)
    W = sum(w for _, w in sw)
    if W <= 0:
        raise ValueError("positive total weight required")
    run = 0
    lo = sw[-1][0]
    for x, w in sw:
        run += w
        if 2 * run >= W:
            lo = x
            break
    run = 0
    hi = sw[0][0]
    for x, w in reversed(sw):
        run += w
        if 2 * run >= W:
            hi = x
            break
    return lo, hi


def weighted_l1(items: Iterable[tuple[int | Fraction, int]], t: Fraction) -> Fraction:
    return sum((q(w) * abs(q(x) - t) for x, w in support_weights(items)), Q(0))


def weighted_mean_variance(items: Iterable[tuple[int | Fraction, int]]) -> tuple[Fraction, Fraction]:
    sw = support_weights(items)
    W = sum(w for _, w in sw)
    S = sum((q(w) * x for x, w in sw), Q(0))
    Q2 = sum((q(w) * x * x for x, w in sw), Q(0))
    mu = S / W
    var = Q2 / W - mu * mu
    return mu, var


def cleared_mean_median_bound(items: Iterable[tuple[int | Fraction, int]]) -> tuple[Fraction, Fraction]:
    sw = support_weights(items)
    W = sum(w for _, w in sw)
    S = sum((q(w) * x for x, w in sw), Q(0))
    Q2 = sum((q(w) * x * x for x, w in sw), Q(0))
    lo, hi = weighted_median_endpoints(sw)
    M = lo + hi  # twice the conventional median
    lhs = (2 * S - M * W) ** 2
    rhs = 4 * (W * Q2 - S * S)
    return lhs, rhs


def sample_median_pmf_numerator(weights: Sequence[int], j: int, N: int) -> int:
    if N % 2 != 1 or N <= 0:
        raise ValueError("N must be positive odd")
    n = (N - 1) // 2
    A = sum(weights[:j])
    B = weights[j]
    C = sum(weights[j + 1 :])
    out = 0
    for i in range(n + 1):
        for k in range(n + 1):
            h = N - i - k
            if h <= 0:
                continue
            multinomial = math.factorial(N) // (
                math.factorial(i) * math.factorial(h) * math.factorial(k)
            )
            out += multinomial * (A**i) * (B**h) * (C**k)
    return out


def sample_median_cdf_numerator(weights: Sequence[int], j: int, N: int) -> int:
    """Numerator of P(M_N <= support[j]) for odd N."""
    if N % 2 != 1 or N <= 0:
        raise ValueError("N must be positive odd")
    n = (N - 1) // 2
    A = sum(weights[: j + 1])
    W = sum(weights)
    return sum(math.comb(N, r) * A**r * (W - A) ** (N - r) for r in range(n + 1, N + 1))


def enumerate_sample_median_numerators(weights: Sequence[int], N: int) -> list[int]:
    out = [0] * len(weights)
    for outcome in itertools.product(range(len(weights)), repeat=N):
        wt = math.prod(weights[i] for i in outcome)
        med = sorted(outcome)[N // 2]
        out[med] += wt
    return out


def median3(a: int, b: int, c: int) -> int:
    return sorted((a, b, c))[1]


def ninther9(xs: Sequence[int]) -> int:
    if len(xs) != 9:
        raise ValueError("ninther9 needs nine entries")
    return median3(
        median3(*xs[0:3]),
        median3(*xs[3:6]),
        median3(*xs[6:9]),
    )


def interpolated_median(m: Fraction, w: Fraction, i: int, j: int, k: int) -> Fraction:
    if j <= 0:
        raise ValueError("median class must be nonempty")
    return m + w * Q(k - i, 2 * j)


def theil_sen_slopes(points: Sequence[tuple[Fraction, Fraction]]) -> list[Fraction]:
    slopes: list[Fraction] = []
    for i in range(len(points)):
        xi, yi = points[i]
        for j in range(i + 1, len(points)):
            xj, yj = points[j]
            if xi != xj:
                slopes.append((yj - yi) / (xj - xi))
    return slopes


@dataclass
class Check:
    name: str
    cases: int
    detail: str


def run_checks() -> dict[str, object]:
    checks: list[Check] = []

    # 1. Balance characterization and L1 minimizer interval.
    cases = 0
    for n in range(1, 8):
        for ys in itertools.combinations_with_replacement(range(5), n):
            lo, hi = median_endpoints(ys)
            candidates = [Q(r, 2) for r in range(-2, 12)]
            vals = {t: l1_objective(ys, t) for t in candidates}
            best = min(vals.values())
            for t in candidates:
                assert is_balance_median(ys, t) == (lo <= t <= hi)
                assert (vals[t] == best) == (lo <= t <= hi)
            assert twice_median(ys) == lo + hi
            cases += 1
    checks.append(Check("finite_balance_and_L1", cases, "all multisets of size <=7 over {0,...,4}"))

    # 2. Weighted finite laws: median interval, L1 minimizers, and mean-median bound.
    cases = 0
    for width in range(1, 6):
        for ws in itertools.product(range(4), repeat=width):
            if sum(ws) == 0:
                continue
            items = [(x, ws[x]) for x in range(width)]
            lo, hi = weighted_median_endpoints(items)
            candidates = [Q(r, 2) for r in range(-2, 2 * width + 1)]
            vals = {t: weighted_l1(items, t) for t in candidates}
            best = min(vals.values())
            for t in candidates:
                below = sum(w for x, w in items if x < t)
                above = sum(w for x, w in items if x > t)
                W = sum(ws)
                is_med = 2 * below <= W and 2 * above <= W
                assert is_med == (lo <= t <= hi)
                assert (vals[t] == best) == (lo <= t <= hi)
            lhs, rhs = cleared_mean_median_bound(items)
            assert lhs <= rhs
            cases += 1
    checks.append(Check("weighted_medians_and_mean_bound", cases, "weights 0..3 on supports of width <=5"))

    # 3. Rank perturbation under at most r coordinate replacements.
    cases = 0
    alphabet = range(4)
    for n in range(1, 6):
        all_samples = list(itertools.product(alphabet, repeat=n))
        for xs in all_samples:
            sx = sorted(xs)
            for ys in all_samples:
                r = sum(a != b for a, b in zip(xs, ys))
                sy = sorted(ys)
                for k in range(n):
                    if r <= k:
                        assert sx[k - r] <= sy[k]
                    if k + r < n:
                        assert sy[k] <= sx[k + r]
                cases += 1
    checks.append(Check("rank_perturbation", cases, "all pairs of samples of size <=5 over four values"))

    # 4. Exact odd sample-median PMF and CDF for finite laws.
    cases = 0
    for s in range(1, 5):
        for weights in itertools.product(range(1, 4), repeat=s):
            W = sum(weights)
            for N in (1, 3, 5):
                enum = enumerate_sample_median_numerators(weights, N)
                assert sum(enum) == W**N
                for j in range(s):
                    assert sample_median_pmf_numerator(weights, j, N) == enum[j]
                    assert sample_median_cdf_numerator(weights, j, N) == sum(enum[: j + 1])
                    cases += 1
    checks.append(Check("exact_sample_median_law", cases, "supports <=4, positive weights <=3, N in {1,3,5}"))

    # 5. Ninther rank guarantee.
    ranks = Counter()
    for p in itertools.permutations(range(9)):
        ranks[ninther9(p)] += 1
    assert min(ranks) == 3 and max(ranks) == 5
    checks.append(Check("ninther_rank", math.factorial(9), "output is always the 4th, 5th, or 6th order statistic"))

    # 6. Majority interval theorem for median filters.
    cases = 0
    for n in (1, 3, 5, 7):
        for xs in itertools.product(range(4), repeat=n):
            lo, hi = median_endpoints(xs)
            for a in range(4):
                for b in range(a, 4):
                    inside = sum(a <= x <= b for x in xs)
                    if 2 * inside > n:
                        assert a <= lo <= hi <= b
                    cases += 1
    checks.append(Check("median_filter_majority", cases, "all odd windows <=7 over four gray levels"))

    # 7. Interpolated median formula and the article's numerical example.
    example = interpolated_median(Q(3), Q(1), 22, 33, 45)
    assert example == Q(221, 66)
    cases = 0
    for i in range(10):
        for j in range(1, 10):
            for k in range(10):
                N = i + j + k
                if not (2 * i <= N and 2 * k <= N):
                    continue
                z = interpolated_median(Q(7, 3), Q(5, 2), i, j, k)
                # Equivalent upper-edge formula: m+w/2-w*(N/2-i)/j complement.
                z2 = Q(7, 3) + Q(5, 4) - Q(5, 2) * Q(j + i - k, 2 * j)
                assert z == z2
                cases += 1
    checks.append(Check("interpolated_median", cases, f"Wikipedia example = {example.numerator}/{example.denominator}"))

    # 8. Symmetry and the finite skew counterexample.
    for c in range(-3, 4):
        for offsets in itertools.product(range(4), repeat=4):
            xs = [Q(c + d) for d in offsets] + [Q(c - d) for d in offsets] + [Q(c)]
            assert conventional_median(xs) == c
            assert sum(xs, Q(0)) / len(xs) == c
    xs = list(map(Q, [0, 0, 1, 1, 2]))
    mu = sum(xs, Q(0)) / len(xs)
    med = conventional_median(xs)
    third = sum(((x - mu) ** 3 for x in xs), Q(0)) / len(xs)
    assert mu == Q(4, 5) and med == 1 and third == Q(18, 125) and mu < med and third > 0
    checks.append(Check("symmetry_and_skew", 7 * 4**4 + 1, "includes positive third moment with mean below median"))

    # 9. Theil-Sen exact recovery on collinear rational data.
    cases = 0
    for a in range(-3, 4):
        for b in range(-2, 3):
            pts = [(Q(x), Q(a * x + b)) for x in range(-3, 4)]
            slopes = theil_sen_slopes(pts)
            assert slopes and all(s == a for s in slopes)
            assert conventional_median(slopes) == a
            cases += 1
    checks.append(Check("theil_sen_collinear", cases, "seven rational points on each of 35 lines"))

    # 10. Replacement breakdown count for the conventional median.
    cases = 0
    for n in range(1, 21):
        need = (n + 1) // 2
        for r in range(0, n + 1):
            xs = [0] * (n - r) + [10**9] * r
            med = conventional_median(xs)
            unbounded_at_scale = med > 0
            assert unbounded_at_scale == (r >= need)
            cases += 1
    checks.append(Check("replacement_breakdown", cases, "n<=20; minimum replacements = ceil(n/2)"))

    return {
        "schema": "median-ipra-validation-v1",
        "arithmetic": "exact integers and fractions only",
        "checks": [c.__dict__ for c in checks],
        "total_cases": sum(c.cases for c in checks),
        "derived_examples": {
            "interpolated_median_22_33_45": {
                "exact": f"{example.numerator}/{example.denominator}",
                "decimal": float(example),
            },
            "skew_counterexample": {
                "sample": [0, 0, 1, 1, 2],
                "mean": "4/5",
                "median": "1",
                "third_central_moment": "18/125",
            },
            "ninther_rank_counts": {str(k + 1): v for k, v in sorted(ranks.items())},
        },
        "status": "PASS",
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = run_checks()
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
