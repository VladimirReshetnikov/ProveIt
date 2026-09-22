#!/usr/bin/env python3
"""Exact finite checks for Expanding Polynomial Dynamics.

Python 3.10+, standard library only. These are regression checks of formal
identities and finite truncations, not a proof of the infinite Hahn statements.
Run without -O: python code/verify.py --output data/verification.json
"""
from __future__ import annotations

import argparse
from fractions import Fraction as Q
from itertools import combinations, product
import json
from pathlib import Path
import platform
from time import perf_counter

Series = list[Q]
Poly = dict[tuple[int, int], Q]
COUNTS: dict[str, int] = {}


def check(condition: bool, category: str) -> None:
    if not condition:
        raise AssertionError(f"Check failed: {category}")
    COUNTS[category] = COUNTS.get(category, 0) + 1


def mul(a: Series, b: Series, n: int) -> Series:
    c = [Q(0)] * (n + 1)
    for i, x in enumerate(a[: n + 1]):
        if x:
            for j, y in enumerate(b[: n + 1 - i]):
                if y:
                    c[i + j] += x * y
    return c


def sqrt_one(a: Series) -> Series:
    """Binomial evaluator, for a[0] == 1."""
    if not a or a[0] != 1:
        raise ValueError("A square-root input must have constant coefficient 1")
    n = len(a) - 1
    u = a.copy()
    u[0] = Q(0)
    result = [Q(1)] + [Q(0)] * n
    power = result.copy()
    choose = Q(1)
    for k in range(1, n + 1):
        power = mul(power, u, n)
        choose *= (Q(1, 2) - (k - 1)) / k
        result = [x + choose * y for x, y in zip(result, power)]
    return result


def nested_center(word: tuple[int, ...], n: int) -> Series:
    """Compose sign*sqrt(1+q*w), with terminal w=0, modulo q^(n+1)."""
    if len(word) < n + 1 or any(s not in (-1, 1) for s in word):
        raise ValueError("At least n+1 binary signs are required")
    w = [Q(0)] * (n + 1)
    for sign in reversed(word):
        a = [Q(1)] + w[:n]
        w = [sign * c for c in sqrt_one(a)]
    return w


def recursive_center(word: tuple[int, ...], n: int) -> Series:
    """Independent coefficient recursion from x_s^2-1=q*x_shift(s)."""
    if len(word) < n + 1 or any(s not in (-1, 1) for s in word):
        raise ValueError("At least n+1 binary signs are required")
    if n == 0:
        return [Q(word[0])]
    tail = recursive_center(word[1:], n - 1)
    out = [Q(word[0])]
    for j in range(1, n + 1):
        cross = sum((out[k] * out[j - k] for k in range(1, j)), Q(0))
        out.append((tail[j - 1] - cross) / (2 * word[0]))
    return out


def iterate_once(a: Series) -> Series:
    """(a^2-1)/q; one coefficient of precision is lost."""
    square = mul(a, a, len(a) - 1)
    if square[0] != 1:
        raise ValueError("This truncation does not have integral image")
    return square[1:]


def p_add(a: Poly, b: Poly) -> Poly:
    c = a.copy()
    for e, x in b.items():
        c[e] = c.get(e, Q(0)) + x
        if not c[e]:
            del c[e]
    return c


def p_scale(a: Poly, scalar: Q) -> Poly:
    return {e: x * scalar for e, x in a.items() if x * scalar}


def p_mul(a: Poly, b: Poly, n: int) -> Poly:
    c: Poly = {}
    for (i, j), x in a.items():
        for (k, l), y in b.items():
            if i + j + k + l <= n:
                e = (i + k, j + l)
                c[e] = c.get(e, Q(0)) + x * y
    return {e: x for e, x in c.items() if x}


def p_sqrt(u: Poly, n: int) -> Poly:
    """sqrt(1+u), total-degree truncation in q, epsilon."""
    if (0, 0) in u:
        raise ValueError("u must have positive total degree")
    out: Poly = {(0, 0): Q(1)}
    power = out.copy()
    choose = Q(1)
    for k in range(1, n + 1):
        power = p_mul(power, u, n)
        choose *= (Q(1, 2) - (k - 1)) / k
        out = p_add(out, p_scale(power, choose))
    return out


def perturbed_center(word: tuple[int, ...], n: int) -> Poly:
    w: Poly = {}
    for sign in reversed(word):
        u = {(i + 1, j): a for (i, j), a in w.items() if i + j + 1 <= n}
        u = p_add(u, {(0, 1): Q(-1)})
        w = p_scale(p_sqrt(u, n), Q(sign))
    return w


def laurent_mul(a: Poly, b: Poly, max_h: int, max_q: int) -> Poly:
    """Here exponents are (h-degree,q-degree); negative q powers allowed."""
    c: Poly = {}
    for (h, q), x in a.items():
        for (hh, qq), y in b.items():
            e = (h + hh, q + qq)
            if e[0] <= max_h and e[1] <= max_q:
                c[e] = c.get(e, Q(0)) + x * y
    return {e: x for e, x in c.items() if x}


def q_inverse(a: Poly) -> Poly:
    return {(h, q - 1): x for (h, q), x in a.items()}


def least_period(word: tuple[int, ...]) -> int:
    n = len(word)
    return next(p for p in range(1, n + 1)
                if n % p == 0 and all(word[j] == word[j % p] for j in range(n)))


def mobius(n: int) -> int:
    answer, p = 1, 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            answer = -answer
            if n % p == 0:
                return 0
        p += 1
    return -answer if n > 1 else answer


def main() -> None:
    if not __debug__:
        raise RuntimeError("Run without -O; exact assertions must stay enabled")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1] / "data/verification.json")
    args = parser.parse_args()
    start = perf_counter()
    order = 7
    words = list(product((-1, 1), repeat=order + 1))
    centers: dict[tuple[int, ...], Series] = {}
    for word in words:
        a = recursive_center(word, order)
        centers[word] = a
        check(a == nested_center(word, order), "independent_center_constructions")
        tail = recursive_center(word[1:], order - 1)
        check(iterate_once(a) == tail, "itinerary_equation")
        s, r, t = word[:3]
        check(a[:3] == [Q(s), Q(s * r, 2), Q(s * r * t, 4) - Q(s, 8)],
              "displayed_first_coefficients")
    for word, other in combinations(words, 2):
        mismatch = next(i for i, (a, b) in enumerate(zip(word, other)) if a != b)
        observed = next(i for i, (a, b) in enumerate(zip(centers[word], centers[other])) if a != b)
        check(observed == mismatch, "exact_first_mismatch_order")

    periodic_counts = {}
    for p in range(1, 7):
        actual_exact = 0
        for word in product((-1, 1), repeat=p):
            wanted = 9
            longword = tuple(word[j % p] for j in range(wanted + p + 1))
            a = recursive_center(longword, wanted + p)
            b = a
            for _ in range(p):
                b = iterate_once(b)
            check(b == a[: wanted + 1], "periodic_identity")
            actual_exact += least_period(word) == p
        expected = sum(mobius(p // e) * 2 ** e for e in range(1, p + 1) if p % e == 0)
        check(actual_exact == expected, "mobius_exact_period_count")
        periodic_counts[str(p)] = {"fixed_by_iterate": 2 ** p,
                                  "exact_period_points": actual_exact,
                                  "exact_period_cycles": actual_exact // p}

    n = 4
    for word in product((-1, 1), repeat=n + 1):
        a = perturbed_center(word, n)
        tail = perturbed_center(word[1:], n - 1)
        residual = p_add(p_mul(a, a, n), {(0, 0): Q(-1), (0, 1): Q(1)})
        residual = p_add(residual, {(i + 1, j): -x for (i, j), x in tail.items()})
        check(not residual, "two_parameter_itinerary_equation")
        unperturbed = recursive_center(word, n)
        check(all(a.get((i, 0), Q(0)) == unperturbed[i] for i in range(n + 1)),
              "perturbation_divisible_by_epsilon")
        check(a.get((0, 1), Q(0)) == Q(-word[0], 2), "leading_perturbation_response")

    plus = recursive_center((1,) * 15, 14)
    check(plus[:9] == [Q(1), Q(1,2), Q(1,8), Q(0), Q(-1,128), Q(0),
                        Q(1,1024), Q(0), Q(-5,32768)], "displayed_fixed_point")
    center: Poly = {(0, j): a for j, a in enumerate(plus) if a}
    h: Poly = {(1, 0): Q(1)}
    rank_two_leading = []
    for step in range(11):
        leading = min(h)
        check(leading == (1, -step), "rank_two_fiber_difference_valuation")
        check(h[leading] == 2 ** step, "rank_two_fiber_leading_coefficient")
        rank_two_leading.append({"iterate": step, "valuation": list(leading),
                                 "coefficient": str(h[leading])})
        # Higher h degrees cannot affect h-degree 1. Discarded high q terms
        # likewise cannot affect the least q exponent at these finite steps.
        h = q_inverse(p_add(p_scale(laurent_mul(center, h, 3, 14), Q(2)),
                              laurent_mul(h, h, 3, 14)))

    # Verify the exact exterior recurrence and its closed formula over integers.
    for degree in range(2, 9):
        for alpha in range(1, 9):
            for kappa in range(1, 9):
                gamma = -alpha
                for step in range(10):
                    expected = -degree ** step * alpha - ((degree ** step - 1) // (degree - 1)) * kappa
                    check(gamma == expected, "exterior_valuation_recurrence")
                    gamma = degree * gamma - kappa
    report = {
        "status": "PASS", "arithmetic": "exact fractions and integer exponent tuples",
        "python": platform.python_version(), "counts": COUNTS,
        "total_checks": sum(COUNTS.values()),
        "periodic_counts": periodic_counts,
        "rank_two_leading_terms": rank_two_leading,
        "fixed_plus_coefficients_through_degree_8": [str(x) for x in plus[:9]],
        "elapsed_seconds": round(perf_counter() - start, 3),
        "limitations": [
            "Finite coefficient tests are not a proof of infinite Hahn summability.",
            "The transfinite-support, topology, compactness, and proper-class results are proved in the article, not checked by this program.",
            "The two center constructions are independent algorithms but share the same mathematical defining equation.",
            "No general surreal canonicalizer, floating-point simulation, or proof-assistant certificate is used."
        ]
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": report["status"], "total_checks": report["total_checks"],
                      "elapsed_seconds": report["elapsed_seconds"], "output": str(args.output)}, indent=2))


if __name__ == "__main__":
    main()
