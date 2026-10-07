#!/usr/bin/env python3
"""Exact coefficients of OEIS A394326, with a_0 = 0 (standard library only).

Run from any working directory, for example::

    python code/exact_coefficients.py --max-weight 65 \
        --output data/exact_coefficients.json

The source definition is credited to Morten Brydensholt's OEIS record,
https://oeis.org/A394326. Sean A. Irvine's jOEIS translation is an inspected
reference specification, not code copied into this implementation:
https://github.com/archmageirvine/joeis/blob/master/src/irvine/oeis/a394/A394326.java

For a ballot row word with prefix counts a >= b >= c, set x=a-b, y=b-c.
The three deficit transitions are
  (x,y) -> (x+1,y), cost 0;
  (x,y) -> (x-1,y+1), cost x-1, if x>0;
  (x,y) -> (x,y-1), cost x+2*y-2, if y>0.
These costs are nonnegative. Remove a path as soon as it first returns to
(0,0), and let I(q) enumerate these first returns. Then C(q)=1-1/I(q).
A primitive return with m copies of each letter has weight at least m-1:
each of its first m-1 letters 3 avoids the origin and has cost at least 1.
Consequently weights <= K require only m <= K+1, hence <= 3*(K+1) steps.
There is no heuristic height cutoff in this program.

Every run checks the available portion of a frozen 40-term source prefix,
the exact reciprocal identity, the primitive support bound, and a short
independent prefix. The independent route enumerates complete tableaux by
ordinary row-word inversions, reverses each finite polynomial, and performs
hard-rod span extraction in the size variable. It also checks finite renewal
and the hook-length total. All checks are explicit exceptions, including
under python -O. Finite checks do not certify asymptotics or all-index signs.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any, Sequence

SOURCE_URL = "https://oeis.org/A394326"
SPECIFICATION_URL = (
    "https://github.com/archmageirvine/joeis/blob/master/"
    "src/irvine/oeis/a394/A394326.java"
)
SPECIFICATION_BLOB = "e59ad7a42e0c96f832b97b6457ea9b5cb1d4a851"
# a(1), ..., a(40): the displayed OEIS prefix recorded during the source
# inspection on 2026-10-03 and checked against the original research probe.
SOURCE_PREFIX = (
    1, 2, 1, 1, 3, 5, 6, 7, 15, 27,
    39, 57, 97, 161, 257, 405, 659, 1076, 1734, 2784,
    4504, 7304, 11813, 19079, 30854, 49947, 80802, 130671,
    211376, 342035, 553403, 895296, 1448462, 2343628,
    3791970, 6135218, 9926549, 16061178, 25987091, 42047032,
)
DEFAULT_MAX_WEIGHT = 65
INDEPENDENT_MAX_WEIGHT = 8


class VerificationError(ValueError):
    """An exact consistency check failed."""


def require_equal(actual: Any, expected: Any, label: str) -> None:
    """Check equality without an assertion that optimization could remove."""
    if actual != expected:
        raise VerificationError(
            f"{label}: expected {expected!r}, obtained {actual!r}"
        )


def _nonnegative_integer(value: int, label: str) -> None:
    if type(value) is not int or value < 0:
        raise ValueError(f"{label} must be a nonnegative integer")


def polynomial_product(
    left: Sequence[int], right: Sequence[int], max_weight: int
) -> list[int]:
    """Multiply integer coefficient arrays modulo q**(max_weight+1)."""
    _nonnegative_integer(max_weight, "max_weight")
    result = [0] * (max_weight + 1)
    for i, x in enumerate(left[: max_weight + 1]):
        if x:
            for j, y in enumerate(right[: max_weight + 1 - i]):
                if y:
                    result[i + j] += x * y
    return result


def cluster_from_first_returns(first_returns: Sequence[int]) -> list[int]:
    """Return C=1-1/I, with I(0)=1, using exact integer arithmetic."""
    if not first_returns or first_returns[0] != 1:
        raise ValueError("the first-return series must have constant term 1")
    if any(type(value) is not int for value in first_returns):
        raise ValueError("first-return coefficients must be integers")
    result = [0] * len(first_returns)
    # I*(1-C)=1, so a_n=I_n-sum_{j=1}^{n-1} I_j*a_{n-j}.
    for n in range(1, len(result)):
        result[n] = first_returns[n] - sum(
            first_returns[j] * result[n - j] for j in range(1, n)
        )
    return result


def primitive_gap_paths(max_weight: int) -> tuple[list[int], list[list[int]]]:
    """Return I(q) and first-return rows indexed by tableau size m.

    Row m stores weights 0..max_weight. Row 0 is identically zero. Every
    return through size max_weight+1 is included. States are sparse integer
    weight dictionaries; no floating-point arithmetic or external input is
    used. The count of letter 1 cannot exceed the largest final size.
    """
    _nonnegative_integer(max_weight, "max_weight")
    max_size = max_weight + 1
    by_size = [[0] * (max_weight + 1) for _ in range(max_size + 1)]
    frontier = {(0, 0): {0: 1}}
    for step in range(1, 3 * max_size + 1):
        following: dict[tuple[int, int], dict[int, int]] = {}
        for (x, y), weights in frontier.items():
            # At the old time step-1, a=(step-1+2*x+y)/3.
            count_a = (step - 1 + 2 * x + y) // 3
            transitions = []
            if count_a < max_size:
                transitions.append((x + 1, y, 0))
            if x:
                transitions.append((x - 1, y + 1, x - 1))
            if y:
                transitions.append((x, y - 1, x + 2 * y - 2))
            for next_x, next_y, cost in transitions:
                if cost < 0:
                    raise VerificationError("a legal deficit cost is negative")
                if cost > max_weight:
                    continue
                target = None
                for weight, count in weights.items():
                    new_weight = weight + cost
                    if new_weight <= max_weight:
                        if target is None:
                            target = following.setdefault((next_x, next_y), {})
                        target[new_weight] = target.get(new_weight, 0) + count
        frontier = following
        if step % 3 == 0:
            size = step // 3
            for weight, count in frontier.pop((0, 0), {}).items():
                if weight < size - 1:
                    raise VerificationError("primitive support W >= m-1 failed")
                by_size[size][weight] = count
        if not frontier:
            break
    totals = [sum(row[w] for row in by_size) for w in range(max_weight + 1)]
    require_equal(totals[0], 1, "unique weight-zero primitive")
    return totals, by_size


def tableau_inversion_polynomial(size: int) -> list[int]:
    """Independently enumerate all (m,m,m) tableaux by ordinary inversions.

    This uses actual row counts and adds b+c, c, or 0 on appending rows
    1, 2, or 3. It permits all intermediate returns and does not use the
    deficit transitions or first-return deletion of the primary generator.
    """
    _nonnegative_integer(size, "size")
    frontier = {(0, 0, 0): {0: 1}}
    for _ in range(3 * size):
        following: dict[tuple[int, int, int], dict[int, int]] = {}
        for (a, b, c), distribution in frontier.items():
            transitions = []
            if a < size:
                transitions.append(((a + 1, b, c), b + c))
            if b < a:
                transitions.append(((a, b + 1, c), c))
            if c < b:
                transitions.append(((a, b, c + 1), 0))
            for counts, increment in transitions:
                target = following.setdefault(counts, {})
                for inversions, count in distribution.items():
                    exponent = inversions + increment
                    target[exponent] = target.get(exponent, 0) + count
        frontier = following
    distribution = frontier.get((size, size, size), {})
    degree = 3 * size * (size - 1) // 2
    require_equal(max(distribution, default=-1), degree, "maximal inversion degree")
    numerator = 2 * math.factorial(3 * size)
    denominator = (
        math.factorial(size) * math.factorial(size + 1) * math.factorial(size + 2)
    )
    hook_count, remainder = divmod(numerator, denominator)
    require_equal(remainder, 0, "integral hook-length count")
    require_equal(sum(distribution.values()), hook_count, "hook-length total")
    return [distribution.get(exponent, 0) for exponent in range(degree + 1)]


def independent_tableau_check(
    max_weight: int, expected_a: Sequence[int], expected_returns: Sequence[Sequence[int]]
) -> dict[str, Any]:
    """Check weights <= max_weight via finite tableaux and span extraction."""
    _nonnegative_integer(max_weight, "max_weight")
    width = max_weight + 1
    all_returns: list[list[int]] = []
    hook_counts = []
    for size in range(max_weight + 2):
        inversion_poly = tableau_inversion_polynomial(size)
        hook_counts.append(sum(inversion_poly))
        reversed_poly = list(reversed(inversion_poly))
        all_returns.append((reversed_poly + [0] * width)[:width])

    # J_m=F_m-sum_{r=1}^{m-1} J_r*F_{m-r} is finite renewal in size.
    primitives = [[0] * width]
    for size in range(1, max_weight + 2):
        primitive = all_returns[size].copy()
        for previous_size in range(1, size):
            product = polynomial_product(
                primitives[previous_size], all_returns[size - previous_size], max_weight
            )
            primitive = [x - y for x, y in zip(primitive, product)]
        require_equal(
            primitive,
            list(expected_returns[size][:width]),
            f"independent primitive polynomial at size {size}",
        )
        primitives.append(primitive)

    # The source's hard-rod definition is Z=1/(1-t-C), Z_n=F_{n+1}.
    # Invert Z in t (not I in q). Then C=1-t-1/Z; its coefficient of
    # t**span is a q-polynomial. Only spans <= weight contribute.
    inverse_z = [[1] + [0] * max_weight]
    spans = [[0] * width]
    for span in range(1, max_weight + 1):
        coefficient = [0] * width
        for j in range(1, span + 1):
            product = polynomial_product(all_returns[j + 1], inverse_z[span - j], max_weight)
            coefficient = [x - y for x, y in zip(coefficient, product)]
        inverse_z.append(coefficient)
        cluster_span = [-value for value in coefficient]
        if span == 1:
            cluster_span[0] -= 1
        require_equal(cluster_span[:span], [0] * span, f"span {span} support")
        spans.append(cluster_span)
    extracted = [sum(row[w] for row in spans) for w in range(width)]
    require_equal(extracted, list(expected_a[:width]), "independent span extraction")
    return {
        "max_weight": max_weight,
        "max_tableau_size": max_weight + 1,
        "a": extracted,
        "tableau_counts_by_size": hook_counts,
        "cluster_coefficients_by_span": spans,
        "checks": {
            "ordinary_inversion_degree": "passed",
            "hook_length_totals": "passed",
            "finite_renewal_by_size": "passed",
            "span_support": "passed",
            "span_extraction": "passed",
        },
    }


def check_source_prefix(coefficients: Sequence[int]) -> int:
    """Check the available source terms; return the number checked."""
    if not coefficients:
        raise VerificationError("the coefficient array is empty")
    require_equal(coefficients[0], 0, "a_0 convention")
    count = min(len(coefficients) - 1, len(SOURCE_PREFIX))
    for n in range(1, count + 1):
        require_equal(coefficients[n], SOURCE_PREFIX[n - 1], f"OEIS source a({n})")
    return count


def generate(max_weight: int = DEFAULT_MAX_WEIGHT) -> dict[str, Any]:
    """Generate a deterministic, verified, JSON-serializable data bundle."""
    _nonnegative_integer(max_weight, "max_weight")
    first_returns, by_size = primitive_gap_paths(max_weight)
    coefficients = cluster_from_first_returns(first_returns)
    source_count = check_source_prefix(coefficients)
    reciprocal = [1] + [-value for value in coefficients[1:]]
    require_equal(
        polynomial_product(first_returns, reciprocal, max_weight),
        [1] + [0] * max_weight,
        "I*(1-C)=1",
    )
    independent = independent_tableau_check(
        min(max_weight, INDEPENDENT_MAX_WEIGHT), coefficients, by_size
    )
    return {
        "schema_version": 1,
        "sequence": "A394326",
        "coefficient_convention": "Array index is n; a(0)=0 is an added convention.",
        "max_weight": max_weight,
        "a": coefficients,
        "I": first_returns,
        "method": {
            "primary": "Exact nonnegative-deficit gap paths stopped at first return; C=1-1/I.",
            "maximum_primitive_size": max_weight + 1,
            "maximum_steps": 3 * (max_weight + 1),
            "truncation_justification": "Each primitive size-m path has weight at least m-1.",
            "arithmetic": "Python arbitrary-precision integers only",
            "independent": "Finite ballot-tableau inversion DP, reversal, renewal, and hard-rod span extraction.",
        },
        "checks": {
            "source_prefix_terms_checked": source_count,
            "source_prefix": "passed",
            "primitive_support": "passed",
            "reciprocal_identity": "passed",
            "independent_prefix": "passed",
        },
        "independent_check": independent,
        "provenance": {
            "primary_record": SOURCE_URL,
            "source_definition_credit": "Morten Brydensholt",
            "reference_implementation": SPECIFICATION_URL,
            "reference_implementation_credit": "Sean A. Irvine, translating Brydensholt's Python",
            "inspected_reference_blob": SPECIFICATION_BLOB,
            "source_prefix": {
                "first_index": 1,
                "last_index": 40,
                "values": list(SOURCE_PREFIX),
                "recorded_on": "2026-10-03",
                "scope": "Frozen 40-term displayed OEIS prefix, transcribed from the checked research probe; no network access occurs in this program.",
            },
            "extension_scope": "Terms beyond 40 are generated here; no b-file verification is claimed.",
            "implementation_note": "Independent implementation of the mathematical model; no third-party program is executed or imported.",
        },
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument(
        "--max-weight", type=int, default=DEFAULT_MAX_WEIGHT,
        help="largest coefficient index, inclusive (default: 65; must be nonnegative)",
    )
    parser.add_argument("--output", type=Path, help="write deterministic JSON here; default is stdout")
    args = parser.parse_args(argv)
    if args.max_weight < 0:
        parser.error("--max-weight must be nonnegative")
    result = generate(args.max_weight)
    serialized = json.dumps(result, indent=2, sort_keys=True, ensure_ascii=True) + "\n"
    if args.output is None:
        print(serialized, end="")
    else:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(serialized, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
