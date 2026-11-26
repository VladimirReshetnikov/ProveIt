#!/usr/bin/env python3
"""Exact finite checks for the positive-type kernel-moment report.

Standard library only. This is computational verification of finite examples,
not a proof of the general theorem and not a Lean build of grh-lean.

Run: python3 verify_rank_moments.py --output rank_moments_results.json
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from collections import Counter
from fractions import Fraction
from math import isqrt, prod
from pathlib import Path


CHECKS = Counter()


def require(condition: bool, category: str) -> None:
    if not condition:
        raise AssertionError(category)
    CHECKS[category] += 1


def rank(columns: tuple[int, ...] | list[int]) -> int:
    """Rank of bit-vector columns over F_2, by exact XOR elimination."""
    pivots: dict[int, int] = {}
    for original in columns:
        v = original
        while v:
            k = v.bit_length() - 1
            if k in pivots:
                v ^= pivots[k]
            else:
                pivots[k] = v
                break
    return len(pivots)


def apply(columns: tuple[int, ...], vector: int) -> int:
    result = 0
    for i, col in enumerate(columns):
        if vector & (1 << i):
            result ^= col
    return result


def dot(x: int, y: int) -> int:
    return (x & y).bit_count() & 1


def symplectic_pair(x: int, y: int) -> int:
    # Standard J=[[0,I_2],[I_2,0]] in characteristic two.
    jy = ((y & 3) << 2) | (y >> 2)
    return dot(x, jy)


def frames(dimension: int, length: int) -> list[tuple[int, ...]]:
    if length == 0:
        return [()]
    return [x for x in itertools.product(range(1, 1 << dimension), repeat=length)
            if rank(x) == length]


def frame_count(q: int, dimension: int, length: int) -> int:
    if length > dimension:
        return 0
    return prod(q ** dimension - q ** i for i in range(length))


def rank_count(q: int, rows: int, columns: int, k: int) -> int:
    numerator = frame_count(q, rows, k) * frame_count(q, columns, k)
    denominator = frame_count(q, k, k)
    require(numerator % denominator == 0, "rank_count_integral")
    return numerator // denominator


def rat(x: Fraction | int) -> str:
    f = Fraction(x)
    return str(f.numerator) if f.denominator == 1 else f"{f.numerator}/{f.denominator}"


def decimal_ceiling(x: Fraction, places: int = 12) -> str:
    """A rigorous decimal upper bound, obtained only with integer arithmetic."""
    require(x >= 0, "decimal_input_nonnegative")
    scale = 10 ** places
    ceiling = (x.numerator * scale + x.denominator - 1) // x.denominator
    return f"{ceiling // scale}.{ceiling % scale:0{places}d}"


def sqrt_decimal_interval(x: Fraction, places: int = 12) -> dict[str, str]:
    """Rigorous enclosing decimal interval for sqrt(x), by integer arithmetic."""
    scale = 10 ** places
    scaled_numerator = x.numerator * scale * scale
    lower = isqrt(scaled_numerator // x.denominator)
    upper = lower + int(lower * lower * x.denominator != scaled_numerator)
    render = lambda z: f"{z // scale}.{z % scale:0{places}d}"
    require(lower * lower * x.denominator <= scaled_numerator <=
            upper * upper * x.denominator, "sqrt_interval")
    return {"lower": render(lower), "upper": render(upper)}


def enumerate_group() -> list[dict]:
    group = []
    for columns in itertools.product(range(16), repeat=4):
        if rank(columns) != 4:
            continue
        images = tuple(apply(columns, v) for v in range(16))
        transposed_images = tuple(sum(dot(col, y) << i for i, col in enumerate(columns))
                                  for y in range(16))
        in_sp = all(symplectic_pair(columns[i], columns[j]) ==
                    symplectic_pair(1 << i, 1 << j)
                    for i in range(4) for j in range(4))
        group.append({"columns": columns, "images": images,
                      "transpose": transposed_images, "in_sp": in_sp})
    require(len(group) == 20160, "GL4_order")
    require(sum(g["in_sp"] for g in group) == 720, "Sp4_order")
    return group


def validate_finite_laws(group: list[dict], a: int, b: int, mixed: bool) -> dict:
    # The mixture is (1/2) Uniform(GL4) + (1/2) Uniform(Sp4).
    # Since |GL4|/|Sp4|=28, its integer weights are 29 on Sp4, 1 outside.
    weights = [1 + 28 * int(g["in_sp"]) if mixed else 1 for g in group]
    denominator = 40320 if mixed else 20160
    require(sum(weights) == denominator, "probability_normalized")
    mask = (1 << b) - 1
    matrix_counts = Counter()
    nullity_counts = Counter()
    for g, w in zip(group, weights):
        compressed = tuple(c & mask for c in g["columns"][:a])
        matrix_counts[compressed] += w
        nullity_counts[a - rank(compressed)] += w

    alphas = {}
    betas = {}
    frame_coeff_checks = 0
    for k in range(1, min(a, b) + 1):
        af = frames(a, k)
        bf = frames(b, k)
        require(len(af) == frame_count(2, a, k), "source_frame_count")
        require(len(bf) == frame_count(2, b, k), "dual_frame_count")
        astab = {x: sum(w for g, w in zip(group, weights)
                        if all(g["images"][v] == v for v in x)) for x in af}
        # Fixed by pi(g)^(-T) iff fixed by pi(g)^T, so no inverses are needed.
        bstab = {y: sum(w for g, w in zip(group, weights)
                        if all(g["transpose"][v] == v for v in y)) for y in bf}
        alphas[k] = Fraction(max(astab.values()), denominator)
        betas[k] = Fraction(max(bstab.values()), denominator)
        require(alphas[k] == betas[k], "rational_radical_special_case")
        # Check every relevant ordered-frame coefficient, squaring the inequality
        # to avoid irrational square roots altogether.
        for x in af:
            for y in bf:
                coefficient = sum(
                    w * (-1 if sum(dot(y_i, g["images"][x_i])
                                   for x_i, y_i in zip(x, y)) % 2 else 1)
                    for g, w in zip(group, weights))
                require(coefficient ** 2 <= 2 ** (4 * k) * astab[x] * bstab[y],
                        "ordered_frame_Fourier_bound")
                frame_coeff_checks += 1

    # In these two group laws all nonzero vectors have stabilizer mass 1/15.
    for v in range(1, 1 << a):
        require(Fraction(sum(w for g, w in zip(group, weights)
                             if g["images"][v] == v), denominator) == Fraction(1, 15),
                "source_vector_transitivity")
    for v in range(1, 1 << b):
        require(Fraction(sum(w for g, w in zip(group, weights)
                             if g["transpose"][v] == v), denominator) == Fraction(1, 15),
                "dual_vector_transitivity")

    moments = []
    tails = []
    for j in range(1, a + 1):
        actual = sum((Fraction(count, denominator) * frame_count(2, nu, j)
                      for nu, count in nullity_counts.items()), Fraction())
        # Independently count the actual independent frames annihilated by each M.
        af = frames(a, j)
        frame_total = 0
        for matrix, count in matrix_counts.items():
            annihilated = sum(all(apply(matrix, v) == 0 for v in t) for t in af)
            require(annihilated == frame_count(2, a - rank(matrix), j),
                    "kernel_frame_identity")
            frame_total += count * annihilated
        require(actual == Fraction(frame_total, denominator), "moment_from_frame_count")

        # Uniform independent-entry matrices give exactly the specified main term.
        uniform_sum = sum(frame_count(2, a - rank(c), j)
                          for c in itertools.product(range(1 << b), repeat=a))
        main = Fraction(frame_count(2, a, j), 2 ** (b * j))
        require(Fraction(uniform_sum, 2 ** (a * b)) == main,
                "independent_entry_moment_identity")
        eps = sum((Fraction(rank_count(2, b, j, k) * 2 ** (2 * k)) * alphas[k]
                   for k in range(1, min(b, j) + 1)), Fraction())
        require(abs(actual - main) <= main * eps, "factorial_moment_bound")
        moments.append({"j": j, "actual": rat(actual), "uniform_main": rat(main),
                        "epsilon": rat(eps), "absolute_error": rat(abs(actual-main)),
                        "error_upper": rat(main*eps)})
        for r in range(j, a + 1):
            probability = Fraction(sum(v for nu, v in nullity_counts.items() if nu >= r),
                                   denominator)
            bound = min(Fraction(1), main * (1 + eps) / frame_count(2, r, j))
            require(probability <= bound, "rank_tail_bound")
            tails.append({"j": j, "r": r, "actual": rat(probability),
                          "upper": rat(bound), "upper_decimal_ceiling": decimal_ceiling(bound)})

    eqnu = sum((Fraction(count, denominator) * 2 ** nu
                for nu, count in nullity_counts.items()), Fraction())
    center = 1 + Fraction(2 ** a - 1, 2 ** b)
    profile_error = Fraction(2 ** a - 1, 15) * (2 ** b - 1) * Fraction(2 ** 2, 2 ** b)
    require(abs(eqnu - center) <= profile_error, "single_vector_profile_moment")
    if a == b:
        singular = Fraction(sum(c for nu, c in nullity_counts.items() if nu >= 1), denominator)
        require(2 * singular <= 2 + Fraction(2 ** (a + 2), 15),
                "original_repository_singular_minor_bound")
    return {
        "law": "half_uniform_GL4_half_uniform_Sp4" if mixed else "uniform_GL4",
        "q": 2, "n": 4, "a": a, "b": b, "weight_denominator": denominator,
        "positive_type_justification": (
            "For every subgroup H, the kernel 1_H(g^-1 h)/|H| is a block Gram "
            "matrix on right cosets. Uniform GL4 and uniform Sp4 therefore have "
            "positive type, and their convex mixture does too."),
        "nullity_distribution": {str(nu): rat(Fraction(count, denominator))
                                 for nu, count in sorted(nullity_counts.items())},
        "distinct_compressions": len(matrix_counts),
        "alpha": {str(k): rat(v) for k, v in alphas.items()},
        "beta": {str(k): rat(v) for k, v in betas.items()},
        "ordered_frame_coefficients_checked": frame_coeff_checks,
        "moments": moments, "tails": tails,
        "single_vector_moment": {"actual": rat(eqnu), "center": rat(center),
                                 "error_upper": rat(profile_error)}}


def large_GL_example(q: int, n: int, a: int, b: int, j: int, r: int) -> dict:
    require(n % 2 == 0, "large_example_even_n")
    eps = sum((Fraction(rank_count(q, b, j, k) * q ** (n*k//2), frame_count(q, n, k))
               for k in range(1, min(b, j)+1)), Fraction())
    main = Fraction(frame_count(q, a, j), q ** (b*j))
    tail = main * (1+eps) / frame_count(q, r, j)
    old_tv_squared = sum((Fraction(rank_count(q, b, a, k) * q ** (n*k),
                                   frame_count(q, n, k) ** 2)
                          for k in range(1, min(a, b)+1)), Fraction()) / 4
    require(a == n-1 and r == a-b+1, "hyperplane_example_dimensions")
    true_tail = Fraction(q ** b - 1, q ** n - 1)
    require(true_tail <= tail, "large_example_tail")
    require(old_tv_squared > 1, "previous_TV_bound_vacuous")
    return {"q": q, "n": n, "a": a, "b": b, "j": j, "r": r,
            "status": "Exact arithmetic using known GL frame orbit counts; GL_n not enumerated.",
            "alpha_beta": "alpha_k=beta_k=1/F_q(n,k)",
            "epsilon": rat(eps), "epsilon_decimal_ceiling": decimal_ceiling(eps),
            "uniform_main_moment": rat(main), "tail_upper": rat(tail),
            "tail_decimal_ceiling_6_places": decimal_ceiling(tail, 6),
            "tail_decimal_ceiling_12_places": decimal_ceiling(tail),
            "previous_TV_bound_squared": rat(old_tv_squared),
            "previous_TV_bound_interval": sqrt_decimal_interval(old_tv_squared),
            "true_hyperplane_tail": rat(true_tail),
            "true_tail_decimal_ceiling": decimal_ceiling(true_tail, 15),
            "true_tail_reason": (
                "A uniform hyperplane contains the fixed projection kernel with "
                "probability (q^b-1)/(q^n-1); then exactly one row of rank is lost.")}


def counterexample() -> dict:
    swap = (2, 1)
    require(apply(swap, 1) == 2, "counterexample_source_not_fixed")
    require(dot(swap[0], 1) == 0 and dot(swap[1], 1) == 1,
            "counterexample_dual_not_fixed")
    actual = Fraction(2)
    center = Fraction(3, 2)
    false_bound = Fraction(0)
    require(abs(actual-center) > false_bound, "counterexample_violates_without_positive_type")
    return {"group": "GL2(F2)", "law": "point mass on the nonidentity swap involution",
            "a": 1, "b": 1, "A_B": "first coordinate injection",
            "alpha": "0", "beta": "0", "actual_E_q_nu": rat(actual),
            "center": rat(center), "false_error_bound": rat(false_bound),
            "PSD_obstruction": "The {identity, swap} principal Gram minor is [[0,1],[1,0]], determinant -1.",
            "interpretation": "Nonnegative, normalized and inverse-symmetric is insufficient."}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("rank_moments_results.json"))
    args = parser.parse_args()
    group = enumerate_group()
    finite_results = [validate_finite_laws(group, a, b, mixed)
                      for a, b in [(2, 2), (3, 2)] for mixed in (False, True)]
    large_results = [large_GL_example(2, 16, 15, 4, 2, 12),
                     large_GL_example(2, 32, 31, 4, 1, 28),
                     large_GL_example(2, 32, 31, 4, 8, 28)]
    counter = counterexample()
    report = {
        "schema_version": 1,
        "description": "Exact finite verification of positive-type kernel-moment certificates.",
        "upstream_repository": "https://github.com/lsernau/grh-lean",
        "upstream_commit": "72fead102f663d5c7a407964a13dc0cf9d977207",
        "source_lemma": "grh-compact/src/New/Heights/OneDeterminant.lean:card_mul_sum_det_le",
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "verification_scope": (
            "All GL4(F2) elements are enumerated. All listed finite probabilities, "
            "moments and inequalities use exact rational/integer arithmetic. GL16 and "
            "GL32 examples use proved orbit-count formulas without enumerating those "
            "groups. Decimal bounds are rounded upward using integer arithmetic. "
            "This does not constitute a Lean build or a general-theorem proof."),
        "finite_group_order": 20160, "symplectic_subgroup_order": 720,
        "finite_results": finite_results, "large_GL_examples": large_results,
        "positive_type_counterexample": counter,
        "checks_by_category": dict(sorted(CHECKS.items())),
        "total_checks": sum(CHECKS.values()), "all_checks_passed": True}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"all_checks_passed": True, "total_checks": report["total_checks"],
                      "finite_cases": len(finite_results),
                      "GL4_elements": len(group), "output": str(args.output)}))


if __name__ == "__main__":
    main()
