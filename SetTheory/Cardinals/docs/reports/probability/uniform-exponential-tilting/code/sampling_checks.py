#!/usr/bin/env python3
"""Exact-rational checks for the bounded-composition PDC theorem.

Python standard library only.  Run from any directory:
    python sampling_checks.py --output ../results

This is a deliberately finite-capacity reference implementation.  It forms
integer weights containing O(capacity * parameter_bits) bits and does NOT
implement the manuscript's binary-size certified-arithmetic sampler.

The mathematical checks use Fraction arithmetic and exhaustive enumeration
or an independent exact coefficient computation.  Seeded sampling is only
a reproducible illustration; exactness of the ideal sampler is proved in
the article and also checked through its exact transition probabilities.
"""

from __future__ import annotations

import argparse
import csv
from fractions import Fraction
from itertools import product
import json
import math
from pathlib import Path
import random
import time


def z_sum(cap: int, q: Fraction) -> Fraction:
    """Geometric sum, using exact rational powers (capacity-dependent cost)."""
    if cap < 0:
        return Fraction(0)
    if q == 1:
        return Fraction(cap + 1)
    return (1 - q ** (cap + 1)) / (1 - q)


def mean_cap(cap: int, q: Fraction) -> Fraction:
    if cap == 0 or q == 0:
        return Fraction(0)
    if q == 1:
        return Fraction(cap, 2)
    power = q ** (cap + 1)
    return q / (1 - q) - (cap + 1) * power / (1 - power)


def variance_cap(cap: int, q: Fraction) -> Fraction:
    if cap == 0 or q == 0:
        return Fraction(0)
    if q == 1:
        return Fraction(cap * (cap + 2), 12)
    power = q ** (cap + 1)
    return q / (1 - q) ** 2 - (cap + 1) ** 2 * power / (1 - power) ** 2


def mean_total(caps: list[int], q: Fraction) -> Fraction:
    return sum((mean_cap(c, q) for c in caps), Fraction(0))


def prepare(caps: list[int], target: int) -> tuple[list[int], int, bool]:
    if not caps or any(not isinstance(c, int) or c < 0 for c in caps):
        raise ValueError("capacities must be a nonempty list of nonnegative integers")
    total = sum(caps)
    if target < 0 or target > total:
        raise ValueError("infeasible target")
    reflect = 2 * target > total
    return caps, total - target if reflect else target, reflect


def certified_lower_tilt(caps: list[int], target: int) -> dict:
    """Exact small-instance bisection returning a certified lower rational tilt.

    The main algorithm in the article replaces the exact mean comparisons
    here by bounded-precision certified comparisons; this reference code is
    only suitable for modest capacities.
    """
    caps, r, reflect = prepare(caps, target)
    active = [c for c in caps if c]
    total = sum(active)
    if r == 0:
        return {"q": Fraction(1), "upper": Fraction(1), "steps": 0,
                "centered_exactly": True, "reflect": reflect, "target": r}
    if 2 * r == total:
        return {"q": Fraction(1), "upper": Fraction(1), "steps": 0,
                "centered_exactly": True, "reflect": reflect, "target": r}
    n = len(active)
    bound = 64 * (n + 1) * total
    bits = (bound - 1).bit_length()
    h = Fraction(1, 1 << bits)
    lo, hi = Fraction(0), Fraction(1)
    steps = 0
    while hi - lo > h:
        mid = (lo + hi) / 2
        mu = mean_total(active, mid)
        steps += 1
        if mu == r:
            lo = hi = mid
            break
        if mu < r:
            lo = mid
        else:
            hi = mid
    assert lo > 0
    assert mean_total(active, lo) <= r <= mean_total(active, hi)
    # log(q_star / q) <= (upper-q)/q <= 1/total, without evaluating logs.
    assert total * (hi - lo) <= lo
    return {"q": lo, "upper": hi, "steps": steps,
            "centered_exactly": lo == hi, "reflect": reflect, "target": r}


def coefficient(caps: list[int], target: int) -> int:
    """Count independently of sampler probabilities; select simple exact routes."""
    total = sum(caps)
    if target < 0 or target > total:
        return 0
    target = min(target, total - target)
    active = [c for c in caps if c]
    if not active:
        return int(target == 0)
    if target == 0:
        return 1
    n = len(active)
    if min(active) >= target:
        return math.comb(target + n - 1, n - 1)
    largest = max(active)
    rest = total - largest
    if rest <= target <= largest:
        j = active.index(largest)
        return math.prod(c + 1 for i, c in enumerate(active) if i != j)
    if len(set(active)) == 1:
        c = active[0]
        return sum((-1) ** k * math.comb(n, k)
                   * math.comb(target - k * (c + 1) + n - 1, n - 1)
                   for k in range(min(n, target // (c + 1)) + 1))
    dp = [0] * (target + 1)
    dp[0] = 1
    for cap in active:
        nxt = [0] * (target + 1)
        window = 0
        for k in range(target + 1):
            window += dp[k]
            if k - cap - 1 >= 0:
                window -= dp[k - cap - 1]
            nxt[k] = window
        dp = nxt
    return dp[target]


def acceptance(caps: list[int], target: int, q: Fraction) -> Fraction:
    caps, r, _ = prepare(caps, target)
    if r == 0:
        return Fraction(1)
    if not 0 < q <= 1:
        raise ValueError("reference routine uses reflected target and 0 < q <= 1")
    j = max(range(len(caps)), key=caps.__getitem__)
    return Fraction(coefficient(caps, r)) * q ** r / math.prod(
        z_sum(c, q) for i, c in enumerate(caps) if i != j)


def enumerate_acceptance(caps: list[int], target: int, q: Fraction) -> dict:
    """Enumerate every possible trial; verify the conditional law exactly."""
    caps, r, reflect = prepare(caps, target)
    j = max(range(len(caps)), key=caps.__getitem__)
    others = [i for i in range(len(caps)) if i != j]
    norm = math.prod(z_sum(caps[i], q) for i in others)
    accepted = {}
    total_mass = Fraction(0)
    for values in product(*(range(caps[i] + 1) for i in others)):
        residual = r - sum(values)
        if residual < 0 or residual > caps[j]:
            continue
        proposal_probability = q ** sum(values) / norm
        accepted_mass = proposal_probability * q ** residual
        x = [0] * len(caps)
        x[j] = residual
        for i, value in zip(others, values):
            x[i] = value
        if reflect:
            x = [c - value for c, value in zip(caps, x)]
        accepted[tuple(x)] = accepted_mass
        total_mass += accepted_mass
    count = coefficient(caps, target)
    assert len(accepted) == count
    assert total_mass == acceptance(caps, target, q)
    assert all(prob / total_mass == Fraction(1, count)
               for prob in accepted.values())
    return {"capacities": caps, "target": target, "q": str(q),
            "states": count, "acceptance": str(total_mass),
            "uniform_probability": str(Fraction(1, count)),
            "all_conditional_probabilities_exactly_equal": True}


def draw_truncated_geom(cap: int, q: Fraction, rng: random.Random) -> int:
    """Exact integer-weight reference; not binary-size in capacity."""
    a, b = q.numerator, q.denominator
    weights = [a ** k * b ** (cap - k) for k in range(cap + 1)]
    ticket = rng.randrange(sum(weights))
    for k, weight in enumerate(weights):
        if ticket < weight:
            return k
        ticket -= weight
    raise AssertionError("unreachable")


def sample_reference(caps: list[int], target: int, q: Fraction,
                     rng: random.Random) -> tuple[list[int], int]:
    caps, r, reflect = prepare(caps, target)
    if r == 0:
        return ([c if reflect else 0 for c in caps], 1)
    j = max(range(len(caps)), key=caps.__getitem__)
    trials = 0
    while True:
        trials += 1
        x = [0] * len(caps)
        for i, c in enumerate(caps):
            if i != j:
                x[i] = draw_truncated_geom(c, q, rng)
        residual = r - sum(x)
        if residual < 0 or residual > caps[j]:
            continue
        probability = q ** residual
        if rng.randrange(probability.denominator) >= probability.numerator:
            continue
        x[j] = residual
        if reflect:
            x = [c - value for c, value in zip(caps, x)]
        assert sum(x) == target and all(0 <= v <= c for v, c in zip(x, caps))
        return x, trials


def log10_fraction(x: Fraction) -> float:
    return math.log10(x.numerator) - math.log10(x.denominator)


def check_modal_variance() -> dict:
    checks = 0
    maximum_ratio = Fraction(0)
    for cap in list(range(0, 17)) + [32, 64, 128]:
        for q in [Fraction(1, 100), Fraction(1, 10), Fraction(1, 3),
                  Fraction(1, 2), Fraction(3, 4), Fraction(9, 10),
                  Fraction(99, 100), Fraction(1)]:
            m = 1 / z_sum(cap, q)
            variance = variance_cap(cap, q)
            assert variance >= 0
            assert m * m * variance <= 1 - m
            if m < 1:
                maximum_ratio = max(maximum_ratio, m * m * variance / (1 - m))
            # Direct moments independently check the geometric derivative formula.
            if cap <= 16:
                probs = [q ** k / z_sum(cap, q) for k in range(cap + 1)]
                mu = sum(Fraction(k) * p for k, p in enumerate(probs))
                direct = sum((Fraction(k) - mu) ** 2 * p for k, p in enumerate(probs))
                assert mu == mean_cap(cap, q) and direct == variance
            checks += 1
    return {"exact_rational_cases": checks, "passed": True,
            "maximum_var_over_bound": float(maximum_ratio)}


def check_general_margins(seed: int, cases: int = 80) -> dict:
    rng = random.Random(seed)
    rows = []
    for case in range(cases):
        n = rng.randrange(2, 11)
        caps = [rng.randrange(1, 17) for _ in range(n)]
        target = rng.randrange(1, sum(caps))
        certificate = certified_lower_tilt(caps, target)
        q = certificate["q"]
        a = acceptance(caps, target, q)
        # e < 3 converts the analytic 5e sqrt(n) bound to an exact comparison.
        assert 225 * n * a * a >= 1
        if certificate["centered_exactly"]:
            assert 25 * n * a * a >= 1
        j = caps.index(max(caps))
        masses = [1 / z_sum(c, q) for c in caps]
        m = masses[j]
        d_eff = sum(((m / mi) ** 2 * (1 - mi) for mi in masses), Fraction(0))
        variance = sum((variance_cap(c, q) for c in caps), Fraction(0))
        assert m * m * variance <= d_eff <= n
        rows.append({"case": case, "capacities": caps, "target": target,
                     "q": str(q), "q_upper": str(certificate["upper"]),
                     "certified_centered_exactly": certificate["centered_exactly"],
                     "bisection_steps": certificate["steps"],
                     "acceptance": float(a), "expected_trials": float(1 / a),
                     "scaled_acceptance_sqrt_n": float(a) * math.sqrt(n),
                     "effective_dimension_bound": float(d_eff),
                     "all_exact_checks_passed": True})
    return {"cases": cases, "seed": seed,
            "minimum_scaled_acceptance": min(row["scaled_acceptance_sqrt_n"] for row in rows),
            "results": rows}


def large_scale_examples() -> list[dict]:
    heterogeneous = [1, 2, 4, 8, 16, 32, 64, 128]
    q_heterogeneous = certified_lower_tilt(heterogeneous, 20)["q"]
    definitions = [
        ("binary_center_100", [1] * 100, 50, Fraction(1), "exact mean center"),
        ("equal_large_center_100", [1000] * 100, 50000, Fraction(1), "exact mean center"),
        ("equal_large_skew_100", [1000] * 100, 100, Fraction(1, 2), "explicit illustrative tilt"),
        ("equal_large_target_one", [1000] * 100, 1, Fraction(1, 101), "explicit illustrative tilt"),
        ("dominant_capacity", [10**9] + [1] * 99, 500000049, Fraction(1), "all proposals feasible"),
        ("heterogeneous_skew", heterogeneous, 20, q_heterogeneous, "certified lower tilt"),
        ("heterogeneous_center", [1, 2, 5, 13, 34, 89], 72, Fraction(1), "exact mean center"),
    ]
    rows = []
    for name, caps, target, q, kind in definitions:
        a = acceptance(caps, target, q)
        old = acceptance(caps, target, Fraction(1))
        rows.append({"name": name, "columns": len(caps), "total": sum(caps),
                     "target": target, "minimum_capacity": min(caps),
                     "maximum_capacity": max(caps), "q": str(q), "tilt_status": kind,
                     "acceptance": float(a), "expected_trials": float(1 / a),
                     "uniform_proposal_log10_acceptance": log10_fraction(old),
                     "log10_improvement_factor": log10_fraction(a / old),
                     "probabilities_computed_exactly": True})
    return rows


def sharpness_examples() -> list[dict]:
    rows = []
    for n in [10, 20, 50, 100, 200, 500, 1000, 2000]:
        a = Fraction(2 * math.comb(n, n // 2), 1 << n)
        expected = float(1 / a)
        asymptotic = math.sqrt(math.pi * n / 8)
        rows.append({"columns": n, "acceptance": float(a),
                     "expected_trials": expected,
                     "sqrt_pi_n_over_8": asymptotic,
                     "ratio_to_asymptotic": expected / asymptotic})
    return rows


def geometric_sharpness_examples() -> list[dict]:
    """Numerical evaluation from an exact coefficient, avoiding huge powers.

    Here cap=n^3 exceeds target=n(n-1), q=(n-1)/n, and the target is
    exponentially close to the tilted mean. Expected trials tend to
    sqrt(2*pi*n). These diagnostic floating-point values are not included
    among the exact-rational theorem checks.
    """
    rows = []
    for n in [5, 10, 20, 50, 100, 200, 500, 1000]:
        cap = n ** 3
        target = n * (n - 1)
        log_q = math.log1p(-1 / n)
        tail = math.exp((cap + 1) * log_q)
        count = math.comb(n * n - 1, n - 1)
        log_a = (math.log(count) + target * log_q - (n - 1) * math.log(n)
                 - (n - 1) * math.log1p(-tail))
        expected = math.exp(-log_a)
        asymptotic = math.sqrt(2 * math.pi * n)
        rows.append({"columns": n, "common_capacity": cap, "target": target,
                     "q": f"{n - 1}/{n}", "expected_trials": expected,
                     "sqrt_two_pi_n": asymptotic,
                     "ratio_to_asymptotic": expected / asymptotic,
                     "evaluation": "floating logarithms from exact binomial coefficient"})
    return rows


def write_csv(path: Path, rows: list[dict]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parents[1] / "results")
    parser.add_argument("--seed", type=int, default=20261008)
    args = parser.parse_args()
    started = time.perf_counter()
    exact_cases = [
        ([1, 1, 1, 1], 2, Fraction(1)),
        ([2, 3, 5], 4, Fraction(3, 4)),
        ([1, 4, 2, 7], 3, Fraction(1, 2)),
        ([9, 1, 1, 2], 6, Fraction(1)),
        ([2, 2, 9, 1], 12, Fraction(2, 3)),
        ([0, 3, 0, 7], 5, Fraction(1)),
    ]
    uniform_checks = [enumerate_acceptance(*case) for case in exact_cases]
    modal = check_modal_variance()
    margins = check_general_margins(args.seed)
    examples = large_scale_examples()
    sharpness = sharpness_examples()
    geometric_sharpness = geometric_sharpness_examples()
    rng = random.Random(args.seed)
    sampled_trials = []
    caps, target = [1, 4, 2, 7], 3
    q = certified_lower_tilt(caps, target)["q"]
    for _ in range(500):
        _, trials = sample_reference(caps, target, q, rng)
        sampled_trials.append(trials)
    result = {
        "status": "all checks passed",
        "arithmetic": "exact fractions for all asserted mathematical comparisons",
        "implementation_scope": "finite-capacity reference; not the binary-size theoretical implementation",
        "uniform_distribution_checks": uniform_checks,
        "modal_variance_checks": modal,
        "arbitrary_margin_bound_checks": margins,
        "large_scale_probability_examples": examples,
        "single_coordinate_scheme_sharpness": sharpness,
        "geometric_sharpness_numerical_illustration": geometric_sharpness,
        "seeded_reference_sampling": {"samples": len(sampled_trials), "seed": args.seed,
                                      "all_outputs_feasible": True,
                                      "observed_mean_trials": sum(sampled_trials) / len(sampled_trials),
                                      "exact_expected_trials": float(1 / acceptance(caps, target, q)),
                                      "purpose": "reproducible illustration only, not a proof of uniformity"},
        "runtime_seconds": time.perf_counter() - started,
    }
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / "sampling_checks.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    write_csv(args.output / "sampling_examples.csv", examples)
    write_csv(args.output / "sampling_sharpness.csv", sharpness)
    write_csv(args.output / "sampling_geometric_sharpness.csv", geometric_sharpness)
    print(json.dumps({"status": result["status"],
                      "uniform_enumeration_cases": len(uniform_checks),
                      "modal_variance_cases": modal["exact_rational_cases"],
                      "arbitrary_margin_cases": margins["cases"],
                      "minimum_scaled_acceptance": margins["minimum_scaled_acceptance"],
                      "reference_samples": len(sampled_trials),
                      "runtime_seconds": result["runtime_seconds"],
                      "output": str(args.output)}, indent=2))


if __name__ == "__main__":
    main()
