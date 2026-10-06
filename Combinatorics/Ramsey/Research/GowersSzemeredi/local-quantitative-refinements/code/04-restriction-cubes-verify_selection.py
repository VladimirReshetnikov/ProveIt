#!/usr/bin/env python3
"""Exact finite checks for the weighted restriction-selection argument.

Only Python's standard library is required. Run:

    python verify_selection.py

The JSON report is printed to standard output; optionally save it with
--report PATH. These finite computations supplement, but do not replace,
the general proof or verify its large-parameter quantitative constants.

We use K(t) = cos(pi*t)^2 with Fourier coefficients
c[-1] = c[1] = 1/4 and c[0] = 1/2. For independently uniform r,s in F_p,
each point x is retained independently with conditional probability
K((r*x+s*phi(x))/p). A tuple survives when EACH DISTINCT POINT it contains
is retained. Thus its actual survival probability is a product over unique
points; repeated tuple entries must not receive independent Bernoulli
decisions. The formal product instead counts every tuple occurrence.

Every expectation below is a Fraction, computed by Fourier orthogonality:
terms survive precisely when both frequency-weighted sums vanish modulo p.
No floating-point arithmetic, trigonometric approximation, or sampling is
used.
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from pathlib import Path
from typing import Iterable


@dataclass(frozen=True)
class Case:
    p: int
    d: int
    points: tuple[int, ...]
    map_name: str
    image: tuple[int, ...]

    @property
    def name(self) -> str:
        return f"p{self.p}_d{self.d}_m{len(self.points)}_{self.map_name}"


def case(p: int, d: int, points: Iterable[int], map_name: str) -> Case:
    points = tuple(sorted(set(points)))
    if map_name == "square":
        image = tuple(x * x % p for x in points)
    elif map_name == "cube":
        image = tuple(x**3 % p for x in points)
    elif map_name == "affine":
        image = tuple((2 * x + 1) % p for x in points)
    elif map_name == "piecewise":
        image = tuple((x * x + (1 if x % 2 else 0)) % p for x in points)
    else:
        raise ValueError(map_name)
    return Case(p, d, points, map_name, image)


CASES = (
    case(3, 2, range(3), "square"),
    case(3, 3, range(3), "square"),
    case(5, 2, range(5), "square"),
    case(5, 3, range(5), "square"),
    case(5, 3, (0, 1, 3, 4), "cube"),
    case(7, 2, range(7), "square"),
    case(7, 3, range(7), "square"),
    case(7, 3, range(7), "cube"),
    case(7, 3, (0, 1, 2, 4, 6), "piecewise"),
    case(7, 2, (1, 2, 4, 6), "affine"),
)


def fraction_text(value: Fraction) -> str:
    return str(value)


def fourier_probability(
    p: int, phi: dict[int, int], multiplicities: tuple[tuple[int, int], ...]
) -> Fraction:
    """Exact E_{r,s} product_x K((r*x+s*phi(x))/p)^multiplicity[x].

    K(t)^k = 4^(-k) sum_{ell=-k}^k binom(2k,k+ell)e(ell*t).
    A dynamic program accumulates the two residues that character
    orthogonality requires to be zero. For ACTUAL tuple survival every
    multiplicity supplied to this function is one.
    """
    distribution = {(0, 0): 1}
    total_multiplicity = 0
    for x, multiplicity in multiplicities:
        assert multiplicity >= 1
        total_multiplicity += multiplicity
        coefficients = (
            (ell, math.comb(2 * multiplicity, multiplicity + ell))
            for ell in range(-multiplicity, multiplicity + 1)
        )
        coefficients = tuple(coefficients)
        updated: dict[tuple[int, int], int] = {}
        for (first, second), weight in distribution.items():
            for ell, coefficient in coefficients:
                state = (
                    (first + ell * x) % p,
                    (second + ell * phi[x]) % p,
                )
                updated[state] = updated.get(state, 0) + weight * coefficient
        distribution = updated
    return Fraction(distribution.get((0, 0), 0), 4**total_multiplicity)


def additive_tuples(points: tuple[int, ...], d: int, p: int):
    """Enumerate all ordered additive 2d-tuples, including repetitions."""
    point_set = set(points)
    for prefix in itertools.product(points, repeat=2 * d - 1):
        last = (sum(prefix[:d]) - sum(prefix[d:])) % p
        if last in point_set:
            yield prefix + (last,)


def two_relation_count(
    p: int, points: tuple[int, ...], v: tuple[int, ...], ell: tuple[int, ...]
) -> int:
    """Exact number with v.dot(x)=ell.dot(x)=0 in points^(2d)."""
    distribution = {(0, 0): 1}
    for first_coefficient, second_coefficient in zip(v, ell):
        updated: dict[tuple[int, int], int] = {}
        for (first, second), count in distribution.items():
            for x in points:
                state = (
                    (first + first_coefficient * x) % p,
                    (second + second_coefficient * x) % p,
                )
                updated[state] = updated.get(state, 0) + count
        distribution = updated
    return distribution.get((0, 0), 0)


@lru_cache(maxsize=None)
def check_rank_bound(p: int, d: int, points: tuple[int, ...]) -> dict:
    """Check every q=1 coefficient vector outside span(v), not a sample."""
    n = 2 * d
    v = (1,) * d + (-1,) * d
    bound = len(points) ** (n - 2)
    largest_count = 0
    vectors_checked = 0
    principal_vectors = 0
    total_nonprincipal_weight = Fraction(0)
    for ell in itertools.product((-1, 0, 1), repeat=n):
        scalar = ell[0] % p
        principal = all(
            coefficient % p == scalar * sign % p
            for coefficient, sign in zip(ell, v)
        )
        if principal:
            principal_vectors += 1
            continue
        # Directly check the claimed invertible 2-by-2 minor as well.
        assert any(
            (v[i] * ell[j] - v[j] * ell[i]) % p
            for i in range(n)
            for j in range(i + 1, n)
        )
        count = two_relation_count(p, points, v, ell)
        assert count <= bound, (p, d, points, ell, count, bound)
        largest_count = max(largest_count, count)
        vectors_checked += 1
        total_nonprincipal_weight += Fraction(
            2 ** ell.count(0), 4**n
        )
    p0 = Fraction(1, 2**n)
    amplification = 1 + Fraction(2, 2**n)
    assert principal_vectors == 3
    assert total_nonprincipal_weight == 1 - p0 * amplification
    return {
        "nonprincipal_vectors_checked": vectors_checked,
        "principal_vectors": principal_vectors,
        "largest_two_relation_solution_count": largest_count,
        "two_relation_solution_bound": bound,
        "total_nonprincipal_coefficient_weight": fraction_text(
            total_nonprincipal_weight
        ),
    }


def check_case(specification: Case) -> dict:
    p, d, points = specification.p, specification.d, specification.points
    assert p > 2 and d >= 2 and points
    n, m = 2 * d, len(points)
    phi = dict(zip(points, specification.image))
    p0 = Fraction(1, 2**n)
    amplification = 1 + Fraction(2, 2**n)
    principal_mass = p0 * amplification
    rank_error = m ** (n - 2)
    repeated_bound = math.comb(n, 2) * rank_error
    h = m ** (n - 1)
    actual_cache: dict[tuple[int, ...], Fraction] = {}
    formal_cache: dict[tuple[tuple[int, int], ...], Fraction] = {}
    totals = Counter()
    expectations = {
        "actual_good": Fraction(0),
        "actual_bad": Fraction(0),
        "formal_good": Fraction(0),
        "formal_bad": Fraction(0),
    }
    for entries in additive_tuples(points, d, p):
        respected = (
            sum(phi[x] for x in entries[:d])
            - sum(phi[x] for x in entries[d:])
        ) % p == 0
        category = "good" if respected else "bad"
        unique_points = tuple(sorted(set(entries)))
        multiplicities = tuple(sorted(Counter(entries).items()))
        if unique_points not in actual_cache:
            actual_cache[unique_points] = fourier_probability(
                p, phi, tuple((x, 1) for x in unique_points)
            )
        if multiplicities not in formal_cache:
            formal_cache[multiplicities] = fourier_probability(
                p, phi, multiplicities
            )
        actual = actual_cache[unique_points]
        formal = formal_cache[multiplicities]
        assert 0 <= formal <= actual <= 1
        if len(unique_points) == n:
            assert actual == formal
            totals["distinct_" + category] += 1
        else:
            totals["repeated_" + category] += 1
        if respected:
            # The principal coefficient vectors survive formally.
            assert formal >= principal_mass
        totals[category] += 1
        expectations["actual_" + category] += actual
        expectations["formal_" + category] += formal

    good_lower = principal_mass * totals["good"]
    formal_bad_upper = p0 * totals["bad"] + rank_error
    # Positivity also permits retaining the exact nonprincipal mass.
    formal_bad_weighted_upper = (
        p0 * totals["bad"] + (1 - principal_mass) * rank_error
    )
    actual_bad_upper = p0 * h + (1 + math.comb(n, 2)) * rank_error
    incisive_actual_bad_upper = (
        formal_bad_weighted_upper + totals["repeated_bad"]
    )
    assert totals["good"] + totals["bad"] <= h
    assert totals["repeated_good"] + totals["repeated_bad"] <= repeated_bound
    assert expectations["actual_good"] >= good_lower
    assert expectations["formal_bad"] <= formal_bad_upper
    assert expectations["formal_bad"] <= formal_bad_weighted_upper
    assert expectations["actual_bad"] <= actual_bad_upper
    assert expectations["actual_bad"] <= incisive_actual_bad_upper
    assert (
        expectations["actual_bad"] - expectations["formal_bad"]
        <= totals["repeated_bad"]
    )
    if specification.map_name == "affine":
        assert totals["bad"] == 0

    # F_3 permits a second exact calculation without Fourier expansion:
    # K(0)=1 and K(1/3)=K(2/3)=1/4.
    direct_checks = 0
    direct_formal_checks = 0
    if p == 3:
        for unique_points, actual in actual_cache.items():
            direct = sum(
                math.prod(
                    Fraction(1) if (r * x + s * phi[x]) % p == 0
                    else Fraction(1, 4)
                    for x in unique_points
                )
                for r in range(p)
                for s in range(p)
            ) / p**2
            assert actual == direct
            direct_checks += 1
        for multiplicities, formal in formal_cache.items():
            direct = sum(
                math.prod(
                    Fraction(1) if (r * x + s * phi[x]) % p == 0
                    else Fraction(1, 4**multiplicity)
                    for x, multiplicity in multiplicities
                )
                for r in range(p)
                for s in range(p)
            ) / p**2
            assert formal == direct
            direct_formal_checks += 1

    return {
        "case": specification.name,
        "p": p,
        "d": d,
        "B": list(points),
        "phi_values_in_B_order": list(specification.image),
        "P0": fraction_text(p0),
        "Q": fraction_text(amplification),
        "H": h,
        "tuple_counts": dict(sorted(totals.items())),
        "expectations": {
            name: fraction_text(value)
            for name, value in expectations.items()
        },
        "bounds": {
            "P0_Q_Tgood": fraction_text(good_lower),
            "formal_bad_P0_Tbad_plus_rank_error": fraction_text(formal_bad_upper),
            "formal_bad_with_exact_nonprincipal_weight": fraction_text(
                formal_bad_weighted_upper
            ),
            "actual_bad_requested_upper": fraction_text(actual_bad_upper),
            "actual_bad_using_exact_repeated_bad_count": fraction_text(
                incisive_actual_bad_upper
            ),
            "repeated_tuple_upper": repeated_bound,
        },
        "slacks": {
            "actual_good_minus_lower": fraction_text(
                expectations["actual_good"] - good_lower
            ),
            "formal_bad_upper_minus_actual": fraction_text(
                formal_bad_upper - expectations["formal_bad"]
            ),
            "actual_bad_upper_minus_actual": fraction_text(
                actual_bad_upper - expectations["actual_bad"]
            ),
        },
        "actual_unique_point_products_checked": len(actual_cache),
        "formal_multiplicity_products_checked": len(formal_cache),
        "independent_direct_F3_checks": direct_checks,
        "independent_direct_formal_F3_checks": direct_formal_checks,
        "rank_checks": check_rank_bound(p, d, points),
        "status": "passed",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", type=Path, help="Also write the JSON report here.")
    arguments = parser.parse_args()
    results = [check_case(specification) for specification in CASES]
    report = {
        "status": "passed",
        "arithmetic": "exact fractions and modular Kronecker constraints",
        "kernel": "cos(pi*t)^2; c0=1/2, c[-1]=c[1]=1/4",
        "cases_checked": len(results),
        "ordered_additive_tuples_checked": sum(
            result["tuple_counts"].get("good", 0)
            + result["tuple_counts"].get("bad", 0)
            for result in results
        ),
        "warning": (
            "Finite q=1 verification supplements the proof. It does not "
            "verify the large-q quantitative restriction constants."
        ),
        "results": results,
    }
    encoded = json.dumps(report, indent=2, sort_keys=True)
    if arguments.report is not None:
        arguments.report.write_text(encoded + "\n", encoding="utf-8")
    print(encoded)


if __name__ == "__main__":
    main()
