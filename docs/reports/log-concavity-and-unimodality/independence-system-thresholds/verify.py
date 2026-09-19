#!/usr/bin/env python3
"""Exact verification for 'Sharp size thresholds for log-concavity failures'.

Python 3.10+; standard library only.  No floating-point decisions are made.
Run: python verify.py --full --output data
The --full option independently enumerates uniform families on at most six
vertices and uniform families containing a fixed core for two exceptional
rank/ground-size cases.  It does NOT enumerate all labelled complexes on seven
vertices.  The general theorems are proved in article.tex, not inferred from tests.
"""
from __future__ import annotations

import argparse
import csv
import json
import platform
from array import array
from fractions import Fraction
from functools import lru_cache
from itertools import combinations
from math import comb
from pathlib import Path
from typing import Iterator

KINDS = ("LC", "OLC", "ULC")


def require(condition: bool, message: object) -> None:
    """A check which is not disabled by python -O."""
    if not condition:
        raise AssertionError(message)


@lru_cache(maxsize=None)
def shadow_minimum(m: int, k: int) -> int:
    """Kruskal--Katona lower shadow, using the canonical k-binomial expansion."""
    if m < 0 or k < 1:
        raise ValueError("m must be nonnegative and k must be positive")
    remaining, result, ceiling = m, 0, None
    for j in range(k, 0, -1):
        if remaining == 0:
            break
        a = j
        while (ceiling is None or a + 1 < ceiling) and comb(a + 1, j) <= remaining:
            a += 1
        require((ceiling is None or a < ceiling) and comb(a, j) <= remaining,
                ("invalid binomial expansion", m, k, remaining, j, ceiling))
        remaining -= comb(a, j)
        result += comb(a, j - 1)
        ceiling = a
    require(remaining == 0, ("nonzero remainder", m, k, remaining))
    return result


def shape_failures(a: list[int], kind: str) -> list[dict[str, int]]:
    """a is padded through its ambient ground-set size, including a_0."""
    n = len(a) - 1
    result = []
    for k in range(1, n):
        left, right = a[k] ** 2, a[k - 1] * a[k + 1]
        if kind == "OLC":
            left *= k
            right *= k + 1
        elif kind == "ULC":
            left *= k * (n - k)
            right *= (k + 1) * (n - k + 1)
        elif kind != "LC":
            raise ValueError(f"unknown shape: {kind}")
        if left < right:
            result.append({"k": k, "left": left, "right": right,
                           "difference": left - right})
    return result


def skeleton_coefficients(n: int, r: int, s: int) -> list[int]:
    if not (n > r >= 2 and 1 <= s <= r - 1):
        raise ValueError("require n > r >= 2 and 1 <= s <= r-1")
    return [comb(n, k) if k <= s else comb(r, k) if k <= r else 0
            for k in range(n + 1)]


def predicted_shapes(n: int, r: int, s: int) -> dict[str, bool]:
    if s == r - 1:
        return dict.fromkeys(KINDS, True)
    lo, mid, hi = comb(n, s), comb(r, s + 1), comb(r, s + 2)
    return {
        "LC": mid * mid >= lo * hi,
        "OLC": (s + 1) * mid * mid >= (s + 2) * lo * hi,
        "ULC": ((s + 1) * (n - s - 1) * mid * mid >=
                (s + 2) * (n - s) * lo * hi),
    }


def skeleton_faces(n: int, r: int, s: int) -> set[int]:
    core = (1 << r) - 1
    return {m for m in range(1 << n) if m & ~core == 0 or m.bit_count() <= s}


def bits(mask: int) -> Iterator[int]:
    while mask:
        bit = mask & -mask
        yield bit
        mask ^= bit


def inspect_system(faces: set[int], n: int) -> dict:
    require(0 in faces, "empty set missing")
    counts = [0] * (n + 1)
    for face in faces:
        require(0 <= face < 1 << n, "out-of-range face")
        counts[face.bit_count()] += 1
        for bit in bits(face):
            require(face ^ bit in faces, ("not downward closed", face, bit))
    gap, witness = 0, None
    for small in faces:
        for large in faces:
            difference = large.bit_count() - small.bit_count()
            if difference > gap and not any((small | bit) in faces
                                            for bit in bits(large & ~small)):
                gap = difference
                witness = [small, large]
    facets = [face for face in faces
              if not any((face | (1 << j)) in faces
                         for j in range(n) if not face & (1 << j))]
    common = (1 << n) - 1
    for face in facets:
        common &= face
    return {"n": n, "rank": max(m.bit_count() for m in faces),
            "coefficients": counts, "face_count": len(faces),
            "augmentation_parameter": gap + 1, "failed_augmentation_witness": witness,
            "facet_masks": sorted(facets), "coloop_mask": common,
            "failures": {kind: shape_failures(counts, kind) for kind in KINDS}}


def hereditary_width(faces: set[int], n: int) -> int:
    width = 0
    for ground in range(1 << n):
        sizes = []
        for face in faces:
            if face & ~ground == 0 and not any((face | bit) in faces
                                              for bit in bits(ground & ~face)):
                sizes.append(face.bit_count())
        width = max(width, max(sizes) - min(sizes))
    return width


def face_vectors(n: int) -> Iterator[list[int]]:
    """All f-vectors with all n singleton faces, not all labelled complexes."""
    def extend(a: list[int], k: int) -> Iterator[list[int]]:
        if k > n:
            yield a
            return
        for m in range(comb(n, k) + 1):
            if shadow_minimum(m, k) <= a[-1]:
                yield from extend(a + [m], k + 1)
    yield from extend([1, n], 2)


def normalize_factor(kind: str, n: int, k: int) -> Fraction:
    if kind == "LC":
        return Fraction(1)
    if kind == "OLC":
        return Fraction(k + 1, k)
    if kind == "ULC":
        return Fraction((k + 1) * (n - k + 1), k * (n - k))
    raise ValueError(kind)


def finite_bounds(n: int, kind: str, rank_lower_bound: int = 0) -> list[dict]:
    records = []
    for k in range(1, n):
        b_range = [n] if k == 1 else range(max(1, comb(rank_lower_bound, k)),
                                          comb(n, k) + 1)
        best = Fraction(-1)
        best_pair = None
        for b in b_range:
            c = max(c for c in range(comb(n, k + 1) + 1)
                    if shadow_minimum(c, k + 1) <= b)
            ratio = Fraction(comb(n, k - 1) * c, b * b) * normalize_factor(kind, n, k)
            if ratio >= best:
                best, best_pair = ratio, (b, c)
        require(best <= 1, ("failed finite bound", n, kind, rank_lower_bound, k, best))
        records.append({"n": n, "kind": kind, "rank_lower_bound": rank_lower_bound,
                        "k": k, "max_ratio": str(best),
                        "maximizing_b": best_pair[0], "maximizing_c": best_pair[1]})
    return records


def subset_masks(n: int, k: int) -> list[int]:
    return [sum(1 << j for j in indices) for indices in combinations(range(n), k)]


def enumerate_uniform_minima(n: int, q: int, core_size: int | None = None) -> dict:
    """Exhaustive shadows; a core forces all its lower faces as well as q-faces."""
    lower = {mask: j for j, mask in enumerate(subset_masks(n, q - 1))}
    upper = subset_masks(n, q)
    base_shadow = 0
    base_count = 0
    if core_size is not None:
        core = (1 << core_size) - 1
        base_count = comb(core_size, q)
        upper = [mask for mask in upper if mask & ~core]
        for mask, j in lower.items():
            if mask & ~core == 0:
                base_shadow |= 1 << j
    single_shadows = []
    for mask in upper:
        value = 0
        for bit in bits(mask):
            value |= 1 << lower[mask ^ bit]
        single_shadows.append(value)
    require(len(lower) <= 64, "array type is too small for shadow universe")
    family_count = 1 << len(upper)
    unions = array("Q", [base_shadow]) * family_count
    minima = [len(lower) + 1] * (len(upper) + 1)
    minima[0] = base_shadow.bit_count()
    for family in range(1, family_count):
        bit = family & -family
        union = unions[family ^ bit] | single_shadows[bit.bit_length() - 1]
        unions[family] = union
        size = family.bit_count()
        count = union.bit_count()
        if count < minima[size]:
            minima[size] = count
    del unions
    if core_size is None:
        for size, minimum in enumerate(minima):
            require(minimum == shadow_minimum(size, q),
                    ("independent shadow mismatch", n, q, size, minimum))
    return {"n": n, "q": q, "core_size": core_size,
            "mandatory_upper_count": base_count, "optional_upper_count": len(upper),
            "families_examined": family_count, "minimum_lower_counts": minima}


def convolution(a: list[int], b: list[int]) -> list[int]:
    result = [0] * (len(a) + len(b) - 1)
    for i, u in enumerate(a):
        for j, v in enumerate(b):
            result[i + j] += u * v
    return result


def write_json(path: Path, obj: object) -> None:
    path.write_text(json.dumps(obj, indent=2) + "\n", encoding="utf-8")


def write_csv(path: Path, records: list[dict]) -> None:
    if not records:
        raise ValueError("cannot write an empty CSV table")
    with path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(records[0]))
        writer.writeheader()
        writer.writerows(records)


def run(output: Path, full: bool) -> dict:
    output.mkdir(parents=True, exist_ok=True)
    report = {"python_version": platform.python_version(), "arithmetic": "exact integers and fractions",
              "full_shadow_enumeration": full}

    certificates = []
    for n in (5, 6, 7):
        faces = skeleton_faces(n, 4, 2)
        certificate = inspect_system(faces, n)
        certificate["face_masks"] = sorted(faces)
        require(certificate["augmentation_parameter"] == 3, certificate)
        require(certificate["coloop_mask"] == 0, certificate)
        certificates.append(certificate)
    write_json(output / "small_counterexamples.json", certificates)

    # Sparse witnesses with 9, 13, and 17 pairs, respectively.
    sparse = []
    removals = {5: [(0, 4)], 6: [(0, 4), (4, 5)],
                7: [(0, 4), (4, 5), (4, 6), (5, 6)]}
    for n, deleted in removals.items():
        faces = skeleton_faces(n, 4, 2)
        for edge in deleted:
            faces.remove(sum(1 << j for j in edge))
        info = inspect_system(faces, n)
        require(info["augmentation_parameter"] == 3, info)
        info["deleted_pairs_one_based"] = [[i + 1, j + 1] for i, j in deleted]
        sparse.append(info)
    write_json(output / "sparse_counterexamples.json", sparse)

    grid = []
    explicit = 0
    for n in range(3, 25):
        for r in range(2, n):
            for s in range(1, r):
                a = skeleton_coefficients(n, r, s)
                predicted = predicted_shapes(n, r, s)
                for kind in KINDS:
                    require(predicted[kind] == (not shape_failures(a, kind)),
                            ("shape classification", n, r, s, kind))
                if n <= 8:
                    info = inspect_system(skeleton_faces(n, r, s), n)
                    require(info["coefficients"] == a and info["augmentation_parameter"] == r - s + 1,
                            ("explicit family", n, r, s, info))
                    require(info["coloop_mask"] == 0, ("coloop", n, r, s))
                    explicit += 1
                    if n <= 6:
                        require(hereditary_width(skeleton_faces(n, r, s), n) == r - s,
                                ("hereditary width", n, r, s))
                grid.append({"n": n, "r": r, "s": s, "lambda": r - s + 1, **predicted})
    write_csv(output / "family_shape_grid.csv", grid)
    report["shape_grid_cases"] = len(grid)
    report["explicit_face_system_checks"] = explicit

    # Direct-sum identities, including nonmatroid summands.
    direct_tests = 0
    for n, r, s in [(3, 2, 1), (4, 3, 1), (4, 3, 2)]:
        left = skeleton_faces(n, r, s)
        for m, rank, skel in [(3, 2, 1), (4, 3, 2)]:
            right = skeleton_faces(m, rank, skel)
            summed = {a | (b << n) for a in left for b in right}
            info = inspect_system(summed, n + m)
            require(info["augmentation_parameter"] == (r - s + 1) + (rank - skel + 1) - 1,
                    ("direct sum", n, r, s, m, rank, skel))
            direct_tests += 1
    report["direct_sum_checks"] = direct_tests

    enumeration, bad_vectors = [], {}
    expected_counts = [1, 2, 5, 16, 70, 457, 4908]
    expected_bad = [(0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0),
                    (0, 0, 5), (0, 3, 47), (23, 120, 809)]
    for n in range(1, 8):
        total = 0
        bad = {kind: [] for kind in KINDS}
        for a in face_vectors(n):
            total += 1
            for kind in KINDS:
                if shape_failures(a, kind):
                    bad[kind].append(a)
        require(total == expected_counts[n - 1], ("face vector count", n, total))
        require(tuple(len(bad[k]) for k in KINDS) == expected_bad[n - 1],
                ("bad vector count", n))
        enumeration.append({"n": n, "face_vectors": total,
                            **{f"fail_{kind}": len(bad[kind]) for kind in KINDS}})
        bad_vectors[str(n)] = bad
    write_csv(output / "face_vector_counts.csv", enumeration)
    write_json(output / "failing_face_vectors.json", bad_vectors)
    report["face_vectors_examined"] = sum(row["face_vectors"] for row in enumeration)

    bounds, bound_details = [], []
    for n, kind, rank in [(6, "LC", 0), (5, "OLC", 0), (2, "ULC", 0),
                          (3, "ULC", 0), (4, "ULC", 0), (7, "LC", 6), (6, "OLC", 5)]:
        bounds += finite_bounds(n, kind, rank)
        for k in range(1, n):
            values = [n] if k == 1 else range(max(1, comb(rank, k)), comb(n, k) + 1)
            for b in values:
                c = max(c for c in range(comb(n, k + 1) + 1)
                        if shadow_minimum(c, k + 1) <= b)
                ratio = Fraction(comb(n, k - 1) * c, b * b) * normalize_factor(kind, n, k)
                require(ratio <= 1, ("individual minimality bound", n, kind, rank, k, b))
                bound_details.append({"n": n, "kind": kind, "rank_lower_bound": rank,
                                      "k": k, "b": b, "U_n_k_b": c, "normalized_ratio": str(ratio)})
    write_csv(output / "minimality_bounds.csv", bounds)
    write_csv(output / "minimality_all_cases.csv", bound_details)
    report["finite_minimality_bounds"] = len(bounds)
    report["individual_minimality_ratios"] = len(bound_details)

    thresholds = []
    codimension_one = []
    totals = []
    for r in range(101):
        total = 2 ** (r + 1) - 1 - comb(r + 1, 2)
        totals.append({"r": r, "N_r": total})
        if r >= 4:
            expected = {"LC": 7 if r in (4, 5) else 8 if r == 6 else r + 1,
                        "OLC": 6 if r == 4 else 7 if r == 5 else r + 1,
                        "ULC": r + 1}
            for kind in KINDS:
                n = next(n for n in range(r + 1, r + 8)
                         if not predicted_shapes(n, r, r - 2)[kind])
                require(n == expected[kind], ("rank threshold", r, kind, n))
            thresholds.append({"r": r, **expected})
        if r >= 3:
            a = skeleton_coefficients(r + 1, r, r - 2)
            require(sum(a) == total, ("total count", r))
            ratio = Fraction(6 * r, r * r - 1)
            require(ratio == Fraction(a[r - 1] ** 2, a[r - 2] * a[r]), ("ratio", r))
            predicted = predicted_shapes(r + 1, r, r - 2)
            require(predicted == {"LC": r <= 6, "OLC": r <= 5, "ULC": r <= 3},
                    ("codimension-one thresholds", r, predicted))
            codimension_one.append({"r": r, "n": r + 1, "total_faces": total,
                                    "a_r_minus_2": a[r - 2], "a_r_minus_1": r,
                                    "a_r": 1, "LC_ratio": str(ratio), **predicted})
    for r in range(97):
        values = [totals[j]["N_r"] for j in range(r, r + 5)]
        require(values[4] == 5 * values[3] - 9 * values[2] + 7 * values[1] - 2 * values[0],
                ("recurrence", r))
    write_csv(output / "rankwise_thresholds.csv", thresholds)
    write_csv(output / "codimension_one_family.csv", codimension_one)
    write_csv(output / "total_face_sequence.csv", totals)

    # Polynomial convolution checks for the two graph families.
    graph_tests = 0
    for r in range(4, 31):
        c = r - 3
        m = comb(r + 1, 2) + 1
        p = convolution([1, 3 + m, 3, 1], [comb(c, k) for k in range(c + 1)])
        require(p[-3:] == [r * r + 1, r, 1], ("graph tail", r, p))
        t, m = 4 * c, 7
        p = convolution([1, 3 + m, 3, 1], [comb(c, k) * t ** k for k in range(c + 1)])
        actual = Fraction(p[-2] ** 2 - p[-3] * p[-1], t ** (2 * c))
        expected = 6 - m + Fraction(3 * c, t) + Fraction(c * (c + 1), 2 * t * t)
        require(actual == expected and actual <= -Fraction(3, 16), ("no-isolates graph", r))
        graph_tests += 2
    report["graph_polynomial_checks"] = graph_tests

    if full:
        shadow_records = []
        for n in range(2, 7):
            for q in range(2, n + 1):
                shadow_records.append(enumerate_uniform_minima(n, q))
        write_json(output / "exhaustive_uniform_shadows.json", shadow_records)
        core_records = []
        for n, r, kind in [(7, 6, "LC"), (6, 5, "OLC")]:
            for q in range(2, r + 1):
                record = enumerate_uniform_minima(n, q, r)
                k = q - 1
                maximum = Fraction(0)
                for extra, lower in enumerate(record["minimum_lower_counts"]):
                    b = n if k == 1 else lower
                    upper = record["mandatory_upper_count"] + extra
                    ratio = Fraction(comb(n, k - 1) * upper, b * b) * normalize_factor(kind, n, k)
                    maximum = max(maximum, ratio)
                    require(ratio <= 1, ("core lower-bound check", n, r, q, extra))
                record["shape_checked"] = kind
                record["maximum_shape_ratio"] = str(maximum)
                core_records.append(record)
        write_json(output / "exhaustive_core_shadows.json", core_records)
        report["unrestricted_uniform_families_examined"] = sum(x["families_examined"] for x in shadow_records)
        report["core_uniform_families_examined"] = sum(x["families_examined"] for x in core_records)
        report["total_uniform_families_examined"] = (report["unrestricted_uniform_families_examined"] +
                                                        report["core_uniform_families_examined"])
    report["status"] = "PASS"
    write_json(output / "verification_report.json", report)
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--full", action="store_true", help="also exhaustively verify small uniform shadows")
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parent / "data")
    args = parser.parse_args()
    print(json.dumps(run(args.output, args.full), indent=2))


if __name__ == "__main__":
    main()
