#!/usr/bin/env python3
"""Exact finite checks for Partition Normal Forms for Small Schur Defect.

These checks supplement the written proofs; they are not a proof for all sets.
Only Python's standard library is required. No floating-point arithmetic is used.
Run from any directory: python3 code/verify.py
"""
from __future__ import annotations

import argparse
import csv
import itertools
import json
import math
import random
import sys
from collections import Counter
from fractions import Fraction
from pathlib import Path
from typing import Iterable, Iterator, Sequence

Number = int | Fraction


def require(condition: bool, message: object) -> None:
    if not condition:
        raise AssertionError(message)


def energy(a: Sequence[Number]) -> int:
    counts = Counter(x - y for x in a for y in a)
    return sum(value * value for value in counts.values())


def energy_by_sums(a: Sequence[Number]) -> int:
    counts = Counter(x + y for x in a for y in a)
    return sum(value * value for value in counts.values())


def maximum_energy(m: int) -> int:
    return (2 * m**3 + m) // 3


def defect(a: Sequence[Number]) -> int:
    numerator = maximum_energy(len(a)) - energy(a)
    require(numerator >= 0 and numerator % 4 == 0, (a, numerator))
    return numerator // 4


def defect_by_triples(a: Sequence[Number]) -> int:
    points = set(a)
    return sum(x + z - y not in points for x, y, z in itertools.combinations(a, 3))


def endpoint_defect(a: Sequence[Number]) -> int:
    points = set(a[:-1])
    endpoint = a[-1]
    return sum(endpoint - x + z not in points
               for z, x in itertools.combinations(a[:-1], 2))


def schur_defect(c: Sequence[Number]) -> int:
    points = set(c)
    return sum(x - y not in points for i, x in enumerate(c) for y in c[:i])


def partitions(r: int, minimum: int = 1) -> Iterator[tuple[int, ...]]:
    if r == 0:
        yield ()
        return
    for first in range(minimum, r + 1):
        for tail in partitions(r - first, first):
            yield (first,) + tail


def holes(mu: Sequence[int]) -> tuple[int, ...]:
    return tuple(part + i for i, part in enumerate(mu))


def hole_weight(h: Sequence[int]) -> int:
    return sum(h) - len(h) * (len(h) - 1) // 2


def kappa(h: Sequence[int]) -> int:
    h = tuple(sorted(h))
    points = set(h)
    result = 0
    for j, hole in enumerate(h, 1):
        for x in range(hole):
            if x in points:
                continue
            overlap = sum(v > hole and v - u == hole - x for u in h for v in h)
            result += (hole + len(h) - j - sum(u <= x for u in h) - overlap)
    return result


def interval_with_holes(top: int, h: Iterable[int]) -> tuple[int, ...]:
    excluded = set(h)
    return tuple(x for x in range(top + 1) if x not in excluded)


def normalized_integer_set(a: Sequence[int]) -> tuple[int, ...]:
    shifted = tuple(x - a[0] for x in a)
    divisor = math.gcd(*shifted)
    return tuple(x // divisor for x in shifted) if divisor else shifted


def models(m: int) -> dict[str, tuple[int, ...]]:
    return {
        "P": interval_with_holes(m - 1, ()),
        "L": interval_with_holes(m, (1,)),
        "R": interval_with_holes(m, (m - 1,)),
        "J_left": interval_with_holes(m, (2,)),
        "J_right": interval_with_holes(m, (m - 2,)),
        "C": interval_with_holes(m + 1, (1, m)),
        "T_left": interval_with_holes(m + 1, (1, 2)),
        "T_right": interval_with_holes(m + 1, (m - 1, m)),
    }


def schur_normal_form(c: Sequence[int], r: int) -> bool:
    unit = c[0]
    if any(x % unit for x in c):
        return False
    shifts = tuple(x // unit - i for i, x in enumerate(c, 1))
    return (all(x >= 0 for x in shifts)
            and all(x <= y for x, y in zip(shifts, shifts[1:]))
            and sum(shifts) == r)


def verify(out: Path, box: int, partition_limit: int) -> dict[str, object]:
    counts: Counter[str] = Counter()
    rows: list[dict[str, object]] = []
    schur_by_size: Counter[int] = Counter()
    energy_by_size: Counter[int] = Counter()
    equality_counts: Counter[str] = Counter()
    candidate_failures: list[object] = []

    # All nonempty subsets of [1, box], not only primitive sets.
    for n in range(1, box + 1):
        for c in itertools.combinations(range(1, box + 1), n):
            r = schur_defect(c)
            counts["schur_sets"] += 1
            if r == 0 or n >= 3 * r + 1:
                require(schur_normal_form(c, r), ("Schur theorem", c, r))
                counts["schur_theorem_instances"] += 1
                schur_by_size[n] += 1
            # This is explicitly a conjecture diagnostic, not an asserted theorem.
            if r >= 1 and n >= 2 * r + 2:
                counts["conjectured_threshold_instances"] += 1
                if not schur_normal_form(c, r):
                    candidate_failures.append([list(c), r])

    # All subsets of [0, box] that contain zero and at least two points.
    for m in range(2, box + 2):
        for rest in itertools.combinations(range(1, box + 1), m - 1):
            a = (0,) + rest
            d = defect(a)
            counts["energy_sets"] += 1
            require(energy(a) == energy_by_sums(a), ("sum/difference", a))
            require(d == defect_by_triples(a), ("ordered triples", a, d))
            require(d == defect(a[:-1]) + endpoint_defect(a), ("recurrence", a))
            c = tuple(sorted(a[-1] - x for x in a[:-1]))
            require(endpoint_defect(a) == schur_defect(c), ("reflection", a))
            norm = normalized_integer_set(a)
            model = models(m)
            if m >= 5:
                if norm != model["P"]:
                    require(d >= m - 2, ("first gap", a, d))
                if d == m - 2:
                    require(norm in (model["L"], model["R"]), ("second level", a))
                if norm not in (model["P"], model["L"], model["R"]):
                    require(d >= 2 * m - 6, ("third lower bound", a, d))
            if m >= 8 and d == 2 * m - 6:
                require(norm in (model["J_left"], model["J_right"], model["C"]),
                        ("third equality", a))
                equality_counts[f"third_m{m}"] += 1
            if m >= 11 and d == 2 * m - 5:
                require(norm in (model["T_left"], model["T_right"]),
                        ("fourth equality", a))
                equality_counts[f"fourth_m{m}"] += 1
            if m >= 11 and d <= 2 * m - 5:
                require(norm in model.values(), ("top four", a, d))
                require(len({x-y for x in a for y in a}) <= 2*m+3,
                        ("difference bound", a))
                energy_by_size[m] += 1
            r = endpoint_defect(a)
            if r >= 1 and m - 1 >= 3 * r + 1:
                require(d >= r * (m - 1 - r), ("endpoint envelope", a, r, d))
                if d == r * (m - 1 - r):
                    require(norm == interval_with_holes(m, (r,)),
                            ("envelope equality", a, r))
                counts["endpoint_envelope_instances"] += 1

    # Every partition through the stated limit, with three exact energy checks.
    for r in range(1, partition_limit + 1):
        for mu in partitions(r):
            h = holes(mu)
            kap = kappa(h)
            require(hole_weight(h) == r, ("weight", mu))
            require(max(h) <= r and len(h) <= r, ("hole budget", h))
            require(kap <= r*r, ("kappa upper bound", h, kap))
            require((kap == r*r) == (h == (r,)), ("kappa equality", h, kap))
            for top in sorted({2 * max(h), 3*r+1+len(h), 3*r+8+len(h)}):
                a = interval_with_holes(top, h)
                require(defect(a) == r*(len(a)-1)-kap, ("hole formula", h, top))
                if top > 2*max(h):
                    require(endpoint_defect(a) == r, ("endpoint weight", h, top))
                counts["hole_formula_instances"] += 1
            n = 3*r+1
            shifts = (0,)*(n-len(mu)) + mu
            c = tuple(i+v for i,v in enumerate(shifts, 1))
            require(schur_defect(c) == r, ("partition converse", mu))
            counts["partition_templates"] += 1
            rows.append({"r": r, "partition": " ".join(map(str, mu)),
                         "holes": " ".join(map(str, h)), "kappa": kap})

    # Families and deliberate sharpness obstructions outside the theorem range.
    for r in range(1, 41):
        c = tuple(x for x in range(1, 2*r+3) if x != r+1)
        require(schur_defect(c) == r, ("threshold obstruction", r))
        require(not schur_normal_form(c, r), ("obstruction lost", r))
        counts["threshold_obstructions"] += 1
    for m in range(5, 71):
        expected = {"P": 0, "L": m-2, "R": m-2,
                    "J_left": 2*m-6, "J_right": 2*m-6, "C": 2*m-6,
                    "T_left": 2*m-5, "T_right": 2*m-5}
        for name, a in models(m).items():
            require(defect(a) == expected[name], ("template energy", m, name))
            counts["energy_template_instances"] += 1

    # Exact rational arithmetic probes: no floating-point comparisons.
    rng = random.Random(20261006)
    for _ in range(700):
        a = tuple(sorted({Fraction(rng.randrange(-60, 61), rng.randrange(1, 9))
                          for _ in range(rng.randrange(3, 15))}))
        if not a:
            continue
        require(defect(a) == defect_by_triples(a), ("rational triples", a))
        if len(a) > 1:
            require(defect(a) == defect(a[:-1]) + endpoint_defect(a),
                    ("rational recurrence", a))
        counts["rational_sets"] += 1
    for r in range(1, 9):
        for mu in partitions(r):
            n = 3*r+1
            shifts = (0,)*(n-len(mu))+mu
            c = tuple(Fraction(7, 11)*(i+x) for i,x in enumerate(shifts, 1))
            require(schur_defect(c) == r, ("rational dilation", mu))
            counts["rational_partition_templates"] += 1

    # Exact vectors demonstrate preservation under an injective rank-one map.
    for m in range(11, 25):
        for name, a in models(m).items():
            v = tuple((2*x+3, -5*x+1, 7*x-4) for x in a)
            multiplicities = Counter(tuple(xi-yi for xi,yi in zip(x,y))
                                     for x in v for y in v)
            require(sum(t*t for t in multiplicities.values()) == energy(a),
                    ("vector embedding", m, name))
            counts["vector_embedding_instances"] += 1

    out.mkdir(parents=True, exist_ok=True)
    with (out / "partition_spectrum.csv").open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=["r", "partition", "holes", "kappa"])
        writer.writeheader()
        writer.writerows(rows)
    report: dict[str, object] = {
        "status": "PASS",
        "scope": "Exact finite checks only; the manuscript supplies general proofs.",
        "python_version": sys.version.split()[0],
        "parameters": {"integer_box": box, "partition_limit": partition_limit,
                       "random_seed": 20261006},
        "counts": dict(sorted(counts.items())),
        "schur_theorem_instances_by_size": dict(sorted(schur_by_size.items())),
        "top_four_instances_by_size": dict(sorted(energy_by_size.items())),
        "equality_instances": dict(sorted(equality_counts.items())),
        "conjectured_threshold_counterexamples_in_checked_box": candidate_failures,
        "conjecture_warning": "Absence of counterexamples is not a proof."
    }
    (out / "verification.json").write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8")
    log = ["ALL EXACT CHECKS PASSED", report["scope"],
           f"Integer box: {box}; partition limit: {partition_limit}"]
    log.extend(f"{key}: {value}" for key, value in sorted(counts.items()))
    log.append(f"Conjecture diagnostic counterexamples: {len(candidate_failures)}")
    (out / "verification.log").write_text("\n".join(map(str, log))+"\n", encoding="utf-8")
    print("\n".join(map(str, log)))
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path,
                        default=Path(__file__).resolve().parents[1] / "data")
    parser.add_argument("--box", type=int, default=16)
    parser.add_argument("--partition-limit", type=int, default=12)
    args = parser.parse_args()
    if not 2 <= args.box <= 20 or not 1 <= args.partition_limit <= 20:
        parser.error("Use 2 <= box <= 20 and 1 <= partition-limit <= 20.")
    verify(args.out, args.box, args.partition_limit)


if __name__ == "__main__":
    main()
