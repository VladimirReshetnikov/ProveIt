#!/usr/bin/env python3
"""Exact checks for Binary Insertion Spectra from a Single Unary Word.

Python 3.10+, standard library only. Finite computations are checks of the
article's proofs, not a proof-assistant formalization. All checks use explicit
exceptions and still execute under python -O.
"""
from __future__ import annotations

import argparse
import csv
import json
import platform
import random
from collections import Counter
from dataclasses import dataclass
from itertools import combinations, product
from math import comb
from pathlib import Path
from typing import Iterable, Iterator

Vector = tuple[int, ...]
INF = 10**9


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def compositions(total: int, parts: int) -> Iterator[Vector]:
    """Weak compositions, in lexicographic order."""
    if total < 0 or parts < 1:
        raise ValueError("total must be nonnegative and parts must be positive")
    if parts == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for tail in compositions(total - first, parts - 1):
            yield (first,) + tail


def word(c: Vector) -> str:
    return "b".join("a" * x for x in c)


def leq(a: Vector, b: Vector) -> bool:
    return all(x <= y for x, y in zip(a, b))


def distance(a: Vector, b: Vector) -> int:
    if len(a) != len(b) or sum(a) != sum(b):
        raise ValueError("distance is defined on equal-sum vectors")
    return sum(max(x - y, 0) for x, y in zip(a, b))


@dataclass(frozen=True)
class Profile:
    m: int
    degrees: tuple[int, ...]

    def __post_init__(self) -> None:
        if self.m < 2 or not self.degrees:
            raise ValueError("m >= 2 and a nonempty degree list are required")
        if any(t < 2 or t > self.m for t in self.degrees):
            raise ValueError("each prescribed degree must lie in [2,m]")

    @property
    def base(self) -> Vector:
        if self.m == 2:
            return (4, 4)
        if self.m == 3:
            return (4, 4, 4)
        extra = max(0, self.m * self.m - 6 * self.m + 3)
        return (2 * self.m + extra, 2 * self.m) + (1,) * (self.m - 2)

    @property
    def centers(self) -> tuple[Vector, ...]:
        q, step = len(self.degrees), 2 * self.m + 1
        b = self.base
        return tuple((b[0] + step * i, b[1] + step * (q - 1 - i))
                     + b[2:] for i in range(q))

    @property
    def deficits(self) -> tuple[Vector, ...]:
        return tuple((self.m - t + 1,) + (1,) * (t - 1)
                     + (0,) * (self.m - t) for t in self.degrees)

    @property
    def special_targets(self) -> tuple[Vector, ...]:
        return tuple(tuple(x - z for x, z in zip(v, delta))
                     for v, delta in zip(self.centers, self.deficits))

    @property
    def total(self) -> int:
        return sum(self.base) + (2 * self.m + 1) * (len(self.degrees) - 1)

    @property
    def length(self) -> int:
        return self.total + self.m - 1

    @property
    def box_size(self) -> int:
        if self.m == 3:
            return comb(5, 2)
        return sum(comb(self.m - 2, s) * (self.m - s + 1)
                   for s in range(self.m - 1))

    @property
    def target_count(self) -> int:
        return comb(self.total - 1, self.m - 1) - len(self.degrees) * (
            self.box_size - 1)

    def membership(self):
        """Return a predicate based on the definition, not predicted degrees."""
        centers = self.centers
        special = set(self.special_targets)
        total = self.total - self.m
        m = self.m

        def accepted(beta: Vector) -> bool:
            if len(beta) != m or min(beta) < 0 or sum(beta) != total:
                return False
            return beta in special or not any(leq(beta, v) for v in centers)
        return accepted


def vector_minimum(c: Vector, deltas: list[tuple[Vector, int]], accepted) -> int:
    """Exhaust all deficit vectors, ordered by cost; no theorem oracle."""
    for delta, cost in deltas:
        if leq(delta, c):
            beta = tuple(x - z for x, z in zip(c, delta))
            if accepted(beta):
                return cost
    return INF


def validate_parameters(p: Profile) -> None:
    m = p.m
    require(p.total > m * (m - 1), "insufficient total for one-run candidates")
    for v, delta in zip(p.centers, p.deficits):
        require(sum(v) == p.total and min(v) > 0, "invalid center")
        require(sum(delta) == m and leq(delta, v), "invalid deficit")
        for j in range(m):
            r = sum(max(v[k] - m + 1, 0) for k in range(m) if k != j)
            require(r > m, "escape margin fails")
    for i, v in enumerate(p.centers):
        for h in range(i):
            require(distance(v, p.centers[h]) > 2 * m, "centers too close")
    for i, beta in enumerate(p.special_targets):
        require(sum(beta) == p.total - m, "wrong target weight")
        for h, v in enumerate(p.centers):
            require(leq(beta, v) == (i == h), "special target contaminates a center")


def verify_profile(p: Profile, enumerate_targets: bool = True) -> dict:
    validate_parameters(p)
    accepted = p.membership()
    deltas = sorted(((delta, sum(x > 0 for x in delta))
                     for delta in compositions(p.m, p.m)), key=lambda z: z[1])
    exceptions = dict(zip(p.centers, p.degrees))
    histogram: Counter[int] = Counter()
    count = 0
    for c in compositions(p.total, p.m):
        actual = vector_minimum(c, deltas, accepted)
        require(actual == exceptions.get(c, 1), f"degree mismatch {p} at {c}")
        histogram[actual] += 1
        count += 1
    require(count == comb(p.length, p.m - 1), "wrong output count")
    target_count = None
    interval_checks = 0
    if enumerate_targets:
        target_count = 0
        base, step, q = p.base, 2 * p.m + 1, len(p.degrees)
        special = set(p.special_targets)
        for beta in compositions(p.total - p.m, p.m):
            direct = accepted(beta)
            target_count += direct
            low = max(0, -((base[0] - beta[0]) // step))
            high = min(q - 1, q - 1 + ((base[1] - beta[1]) // step))
            safe = any(beta[j] > base[j] for j in range(2, p.m)) or low > high
            require(direct == (beta in special or safe), "interval membership fails")
            interval_checks += 1
        require(target_count == p.target_count, "target-count formula fails")
    return {"m": p.m, "degrees": list(p.degrees), "T": p.total,
            "output_length": p.length, "base_center": list(p.base),
            "all_outputs_checked": count, "degree_histogram": dict(histogram),
            "target_count_formula": p.target_count,
            "target_count_enumerated": target_count,
            "interval_membership_comparisons": interval_checks,
            "deficits_per_full_minimization": len(deltas),
            "method": "cost-ordered exhaustive deficit minimization"}


def mask_outputs(u: str, v: str) -> dict[str, int]:
    result: dict[str, int] = {}
    n = len(u) + len(v)
    for chosen in combinations(range(n), len(u)):
        positions = set(chosen)
        i = j = runs = 0
        last_a = False
        out = []
        for pos in range(n):
            take_a = pos in positions
            if take_a:
                out.append(u[i]); i += 1
                runs += not last_a
            else:
                out.append(v[j]); j += 1
            last_a = take_a
        w = "".join(out)
        cost = max(1, runs)
        result[w] = min(result.get(w, INF), cost)
    return result


def dp_degree(u: str, v: str, w: str) -> int:
    """Independent source-assignment DP, using literal letters, not gaps."""
    if len(w) != len(u) + len(v):
        return INF
    states = {(0, 0, False): 0}
    for letter in w:
        following: dict[tuple[int, int, bool], int] = {}
        for (i, j, last_a), cost in states.items():
            if i < len(u) and u[i] == letter:
                state = (i + 1, j, True)
                following[state] = min(following.get(state, INF),
                                       cost + (not last_a))
            if j < len(v) and v[j] == letter:
                state = (i, j + 1, False)
                following[state] = min(following.get(state, INF), cost)
        states = following
    return max(1, min(states.values(), default=INF))


def literal_worked_example(out: Path) -> dict:
    p = Profile(3, (3,))
    accepted = p.membership()
    betas = [b for b in compositions(9, 3) if accepted(b)]
    outputs = [word(c) for c in compositions(12, 3)]
    combined: dict[str, int] = {}
    pair_histograms = []
    comparisons = 0
    for beta in betas:
        v = word(beta)
        by_masks = mask_outputs("aaa", v)
        histogram = dict(sorted(Counter(by_masks.values()).items()))
        require(histogram == {1: 3, 2: 6, 3: 1}, "singleton histogram mismatch")
        pair_histograms.append(histogram)
        for w in outputs:
            dp = dp_degree("aaa", v, w)
            require(dp == by_masks.get(w, INF), "DP/mask disagreement")
            comparisons += 1
        for w, cost in by_masks.items():
            combined[w] = min(combined.get(w, INF), cost)
    require(set(combined) == set(outputs), "literal full-output coverage failed")
    require(Counter(combined.values()) == Counter({1: 90, 3: 1}),
            "worked histogram failed")
    require(combined[word((4, 4, 4))] == 3, "worked exceptional degree failed")
    with (out / "worked_targets.csv").open("w", newline="") as f:
        writer = csv.writer(f); writer.writerow(["gap1", "gap2", "gap3", "word"])
        writer.writerows([*b, word(b)] for b in betas)
    with (out / "worked_outputs.csv").open("w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(["gap1", "gap2", "gap3", "word", "degree"])
        writer.writerows([*c, word(c), combined[word(c)]]
                         for c in compositions(12, 3))
    return {"targets": len(betas), "outputs": len(combined),
            "source_assignment_masks": len(betas) * comb(14, 3),
            "independent_dp_comparisons": comparisons,
            "every_pair_histogram": {1: 3, 2: 6, 3: 1},
            "aggregate_histogram": dict(Counter(combined.values())),
            "exception": word((4, 4, 4))}


def check_histograms() -> dict:
    composition_comparisons = 0
    for m in range(1, 9):
        for d in range(1, 8):
            counts = Counter(sum(x > 0 for x in delta)
                             for delta in compositions(m, d))
            expected = {r: comb(d, r) * comb(m - 1, r - 1)
                        for r in range(1, min(m, d) + 1)}
            require(dict(counts) == expected, "general histogram formula failed")
            require(sum(counts.values()) == comb(m + d - 1, d - 1),
                    "Vandermonde count failed")
            composition_comparisons += 1
    polynomial_coefficients = 0
    for m in range(2, 41):
        n = m - 1
        for k in range(n + 1):
            actual = sum((-1) ** (k - j) * comb(n, j) * comb(n + j + 1, n)
                         * comb(n - j, k - j) for j in range(k + 1))
            expected = comb(n, k) * comb(n + 1, k + 1)
            require(actual == expected, "Rodrigues/Mobius identity failed")
            polynomial_coefficients += 1
    return {"composition_histograms": composition_comparisons,
            "exact_polynomial_coefficients": polynomial_coefficients,
            "largest_polynomial_degree": 40,
            "note": "root location follows from the written orthogonality proof"}


def check_large_parameters() -> dict:
    parameter_cases = 0
    sampled_outputs = 0
    rng = random.Random(20260928)
    for m in range(2, 81):
        for q in (1, 2, 5, 11):
            degrees = tuple(2 + (i * 7) % (m - 1) for i in range(q))
            p = Profile(m, degrees)
            validate_parameters(p)
            if m >= 6 and q == 1:
                require(p.length == m * m, "sharp size construction fails")
            # These are samples, not exhaustive checks of large output classes.
            accepted = p.membership()
            exceptions = set(p.centers)
            for _ in range(40):
                # Uniform stars-and-bars sampling of a weak composition.
                bars = sorted(rng.sample(range(p.total + m - 1), m - 1))
                points = [-1] + bars + [p.total + m - 1]
                c = tuple(points[j + 1] - points[j] - 1 for j in range(m))
                if c not in exceptions:
                    possible = any(c[j] >= m and accepted(tuple(
                        c[k] - (m if k == j else 0) for k in range(m)))
                                   for j in range(m))
                    require(possible, "sampled one-run certificate fails")
                sampled_outputs += 1
            parameter_cases += 1
    return {"parameter_cases": parameter_cases, "maximum_m": 80,
            "sampled_outputs": sampled_outputs, "seed": 20260928,
            "sampling_is_exhaustive": False}


def check_lower_bound_obstructions() -> dict:
    bounded_levels = 0
    boundary_witnesses = 0
    for m in range(3, 8):
        for d in range(m, m + 3):
            # Count all bounded compositions by polynomial convolution.
            coefficients = [1]
            for _ in range(d):
                new = [0] * (len(coefficients) + m - 1)
                for i, value in enumerate(coefficients):
                    for j in range(m):
                        new[i + j] += value
                coefficients = new
            for T in range(m, d * (m - 1)):
                require(coefficients[T] >= d, "interior cube multiplicity fails")
                bounded_levels += 1
            v = (m - 1,) * d
            c = (m, m - 2) + (m - 1,) * (d - 2)
            beta = (0, m - 2) + (m - 1,) * (d - 2)
            require(sum(v) == sum(c), "boundary witness has wrong weight")
            require(dp_degree("a" * m, word(beta), word(v)) == 2,
                    "boundary center must get degree at most two")
            require(dp_degree("a" * m, word(beta), word(c)) == 1,
                    "boundary neighbor must be a one-run insertion")
            boundary_witnesses += 1
    # Guardrail against the tempting but false linear-size extrapolation.
    bad_center = (12, 12, 1, 1, 1, 1)
    capped_output = (5, 5, 5, 5, 4, 4)
    require(sum(bad_center) == sum(capped_output), "guardrail weight mismatch")
    require(max(capped_output) < 6 and capped_output != bad_center,
            "guardrail must have no possible one-run deletion")
    return {"bounded_composition_levels": bounded_levels,
            "boundary_DP_witnesses": boundary_witnesses,
            "undersized_two_large_gaps_rejected": True}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path,
                        default=Path(__file__).resolve().parents[1] / "data")
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    cases: list[Profile] = [Profile(2, (2,) * q) for q in (1, 2, 5)]
    cases += [Profile(3, tuple(ds)) for q in (1, 2, 3)
              for ds in product((2, 3), repeat=q)]
    cases += [Profile(4, ds) for ds in ((2,), (3,), (4,), (2, 4), (3, 3), (2, 3, 4))]
    cases += [Profile(5, (5,)), Profile(5, (2, 5)), Profile(6, (6,))]
    rows = []
    for p in cases:
        row = verify_profile(p)
        rows.append(row)
        print(f"PASS m={p.m}, profile={p.degrees}, N={p.length}: "
              f"{row['all_outputs_checked']} outputs", flush=True)
    receipt = {
        "status": "all checks passed",
        "python_version": platform.python_version(),
        "proof_assistant_checked": False,
        "exhaustive_profiles": rows,
        "exhaustive_profile_count": len(rows),
        "total_profile_output_comparisons": sum(r["all_outputs_checked"] for r in rows),
        "total_interval_membership_comparisons": sum(
            r["interval_membership_comparisons"] for r in rows),
        "literal_worked_example": literal_worked_example(args.out),
        "histogram_checks": check_histograms(),
        "large_parameter_checks": check_large_parameters(),
        "lower_bound_checks": check_lower_bound_obstructions(),
    }
    (args.out / "verification.json").write_text(json.dumps(receipt, indent=2) + "\n")
    with (args.out / "profile_checks.csv").open("w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(["m", "prescribed_degrees", "T", "N", "outputs", "targets"])
        for row in rows:
            writer.writerow([row["m"], ";".join(map(str, row["degrees"])), row["T"],
                             row["output_length"], row["all_outputs_checked"],
                             row["target_count_formula"]])
    print(json.dumps({k: v for k, v in receipt.items()
                      if k not in {"exhaustive_profiles"}}, indent=2), flush=True)


if __name__ == "__main__":
    main()
