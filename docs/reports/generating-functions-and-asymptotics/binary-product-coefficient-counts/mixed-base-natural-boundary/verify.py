#!/usr/bin/env python3
"""Exact verification for interleaved geometric coefficient counts.

Python 3.10+, standard library only. No floating-point arithmetic is used
in any mathematical check. Run from any directory; artifacts are written
next to this script. This is supporting computation, not a proof of an
infinite statement.
"""
from __future__ import annotations

import argparse
import csv
import json
import platform
import random
import time
from collections import Counter
from collections.abc import Iterator
from pathlib import Path


def check_nat(value: int, name: str) -> None:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise ValueError(f"{name} must be a nonnegative integer")


def check_base(base: int) -> None:
    if not isinstance(base, int) or isinstance(base, bool) or base < 3:
        raise ValueError("base must be an integer >= 3")


def gap(base: int, r: int) -> int:
    """Gap at a binary carry of length r in the base-b digit set {0,1}."""
    check_base(base)
    check_nat(r, "r")
    return ((base - 2) * pow(base, r) + 1) // (base - 1)


def threshold(base: int, m: int) -> int:
    """Least r with gap(base,r) >= 2**m, using integer arithmetic only."""
    check_base(base)
    check_nat(m, "m")
    target, r, current = 1 << m, 0, 1
    while current < target:
        current = base * current - 1
        r += 1
    return r


def ones_formula(base: int, m: int, n: int) -> int:
    """Ones in prod(i<m)(1+x^(2^i))*prod(j<n)(1+x^(base^j))."""
    check_base(base)
    check_nat(m, "m")
    check_nat(n, "n")
    if m == 0:
        return 1 << n
    if n == 0:
        return 1 << m
    return 1 << (1 + max(0, n - threshold(base, m)))


def iter_even_counts(base: int, max_n: int) -> Iterator[int]:
    """Stream a(0),...,a(max_n) in O(max_n) big-integer updates.

    h is the first digital gap reaching the current binary interval length.
    At most one new gap level is needed when that length doubles.
    """
    check_base(base)
    check_nat(max_n, "max_n")
    yield 1
    if max_n == 0:
        return
    h, target, a = base - 1, 2, 2
    yield a
    for _n in range(1, max_n):
        target <<= 1
        if h < target:
            h = base * h - 1
        else:
            a <<= 1
        yield a


def coefficient_count(base: int, N: int) -> int:
    check_nat(N, "N")
    return ones_formula(base, (N + 1) // 2, N // 2)


def exponents(base: int, N: int) -> list[int]:
    check_base(base)
    check_nat(N, "N")
    return [pow(2 if j % 2 == 0 else base, j // 2) for j in range(N)]


def dense_counts(base: int, max_N: int, max_degree: int = 3_000_000) -> list[int]:
    """Independent full polynomial multiplication, with exact integer coefficients."""
    if sum(exponents(base, max_N)) > max_degree:
        raise ValueError("Dense polynomial would exceed max_degree")
    coefficients = [1]
    out = [1]
    for g in exponents(base, max_N):
        new = coefficients + [0] * g
        for i, c in enumerate(coefficients):
            new[i + g] += c
        coefficients = new
        out.append(coefficients.count(1))
    return out


def digit_sums(base: int, n: int) -> list[int]:
    check_base(base)
    check_nat(n, "n")
    if n > 22:
        raise ValueError("Explicit digit-sum enumeration is limited to n <= 22")
    sums, power = [0], 1
    for _ in range(n):
        # This concatenation is sorted: power exceeds the previous maximum.
        sums += [x + power for x in sums]
        power *= base
    return sums


def interval_histogram(base: int, m: int, n: int) -> dict[int, int]:
    """Independent event sweep; counts all multiplicities, without gap formula.

    A half-open real interval [s,s+2**m) contains exactly the relevant
    integer exponents, so integer event distances count integer positions.
    Zero coefficients are omitted from the returned histogram.
    """
    check_nat(m, "m")
    events: Counter[int] = Counter()
    length = 1 << m
    for s in digit_sums(base, n):
        events[s] += 1
        events[s + length] -= 1
    histogram: Counter[int] = Counter()
    previous, height = 0, 0
    for position, delta in sorted(events.items()):
        if height > 0:
            histogram[height] += position - previous
        height += delta
        previous = position
    assert height == 0
    return dict(sorted(histogram.items()))


def ternary_even_without_logs(n: int) -> int:
    """Independent evaluation of 2**floor((n+1)*(1-log_3(2))).

    For n>=2, find s=ceil(log_3(2**(n+1))) by exact integer comparisons.
    n=0,1 are the two initial values in the theorem.
    """
    check_nat(n, "n")
    if n < 2:
        return 1 << n
    target, power, s = 1 << (n + 1), 1, 0
    while power < target:
        power *= 3
        s += 1
    return 1 << (n + 1 - s)


def full_from_even(base: int, N: int) -> int:
    """Coefficient of the exact parity generating-function identity."""
    if N % 2 == 0:
        return coefficient_count(base, N)
    n = N // 2
    correction = int(N == 1 or (N == 3 and base <= 4)
                     or (N in (5, 7) and base == 3))
    return coefficient_count(base, 2 * n + 2) // 2 + correction


def run_checks(quick: bool = False) -> dict:
    start = time.perf_counter()
    checks: dict[str, dict] = {}

    max_N = 22 if quick else 28
    dense = dense_counts(3, max_N)
    for N, value in enumerate(dense):
        assert value == coefficient_count(3, N), (N, value)
    checks["dense_ternary"] = {
        "max_N": max_N, "cases": len(dense),
        "largest_degree": sum(exponents(3, max_N)), "passed": True,
    }

    cases = 0
    grid_max = 7 if quick else 10
    for base in range(3, 13):
        for n in range(grid_max + 1):
            for m in range(grid_max + 1):
                hist = interval_histogram(base, m, n)
                assert hist.get(1, 0) == ones_formula(base, m, n), (base,m,n)
                # Total coefficient mass is the number of subsets.
                assert sum(k * v for k, v in hist.items()) == 1 << (m + n)
                cases += 1
    checks["independent_event_sweep_grid"] = {
        "bases": [3,12], "m_range": [0,grid_max], "n_range": [0,grid_max],
        "cases": cases, "passed": True,
    }

    randomizer = random.Random(20260919)
    random_cases = 30 if quick else 150
    max_digits = 11 if quick else 15
    for _ in range(random_cases):
        base = randomizer.randint(3, 40)
        m = randomizer.randint(0, 30)
        n = randomizer.randint(0, max_digits)
        hist = interval_histogram(base, m, n)
        assert hist.get(1, 0) == ones_formula(base, m, n), (base,m,n)
        assert sum(k * v for k, v in hist.items()) == 1 << (m + n)
    checks["random_event_sweep"] = {
        "seed": 20260919, "cases": random_cases, "bases": [3,40],
        "m_range": [0,30], "n_range": [0,max_digits], "passed": True,
    }

    gap_cases = 0
    for base in range(3, 16):
        for n in range(1, 13):
            sums = digit_sums(base, n)
            actual = Counter(y - x for x, y in zip(sums, sums[1:]))
            expected = Counter({gap(base,r): 1 << (n-r-1) for r in range(n)})
            assert actual == expected
            for j, (x,y) in enumerate(zip(sums,sums[1:]), start=1):
                r = (j & -j).bit_length() - 1
                assert y-x == gap(base,r)
            gap_cases += 1
    checks["explicit_gap_distribution"] = {
        "bases": [3,15], "n_range": [1,12], "cases": gap_cases, "passed": True,
    }

    limit = 300 if quick else 2000
    for n in range(limit + 1):
        assert ternary_even_without_logs(n) == coefficient_count(3, 2*n)
    checks["ternary_closed_form"] = {"n_range": [0,limit], "cases": limit+1, "passed": True}

    # Verify the first-order exact gap-threshold update, ratio property,
    # parity identity, and the original order-four recurrence.
    family_cases = 0
    for base in range(3, 65):
        r, g = 1, base - 1
        for n in range(1, 301):
            assert r == threshold(base, n)
            assert coefficient_count(base,2*n) == 1 << (n-r+1)
            prev = coefficient_count(base, 2*(n-1))
            current = coefficient_count(base, 2*n)
            assert current in (prev, 2*prev)
            if g < 1 << (n+1):
                r += 1
                g = base*g - 1
            family_cases += 1
        for n, a in enumerate(iter_even_counts(base, 600)):
            assert a == coefficient_count(base, 2*n)
        for N in range(601):
            assert coefficient_count(base,N) == full_from_even(base,N)
        gs = exponents(base, 80)
        for j in range(76):
            assert gs[j+4] == (base+2)*gs[j+2] - 2*base*gs[j]
    checks["family_identities"] = {
        "bases": [3,64], "even_n_range": [1,300], "even_cases": family_cases,
        "parity_N_range": [0,600], "streaming_n_range": [0,600],
        "exponent_recurrence_terms": 80, "passed": True,
    }

    rational_cases = 0
    for d in range(2,11):
        base = 1 << d
        for n in range(601):
            a = coefficient_count(base,2*n)
            assert a == 1 << (n - n//d)
            assert coefficient_count(base,2*(n+d)) == (1 << (d-1))*a
            rational_cases += 1
    checks["power_of_two_rational_subfamily"] = {
        "d_range": [2,10], "n_range": [0,600], "cases": rational_cases, "passed": True,
    }

    return {
        "project": "Interleaved geometric coefficient counts",
        "arithmetic": "exact integers only",
        "python_version": platform.python_version(),
        "quick_mode": quick, "all_passed": True, "checks": checks,
        "elapsed_seconds": round(time.perf_counter()-start, 3),
        "scope": "Finite verification supports, but does not replace, the proofs in article.tex.",
    }


def write_data(directory: Path) -> None:
    directory.mkdir(parents=True, exist_ok=True)
    with (directory / "binary_ternary_counts.csv").open("w", newline="", encoding="utf-8") as stream:
        writer = csv.writer(stream)
        writer.writerow(["N", "G_N_or_0_at_N0", "number_of_coefficients_equal_to_1"])
        for N in range(401):
            g = 0 if N == 0 else pow(2 if N % 2 else 3, (N-1)//2)
            writer.writerow([N,g,coefficient_count(3,N)])
    with (directory / "even_counts_b3.txt").open("w", encoding="utf-8") as stream:
        stream.write("# a(n) = number of ones in prod(j=0..n-1)(1+x^(2^j))(1+x^(3^j))\n")
        stream.write("# This is an OEIS-style data file; no OEIS identifier is claimed.\n")
        for n in range(1001):
            stream.write(f"{n} {coefficient_count(3,2*n)}\n")
    with (directory / "base_comparison.csv").open("w", newline="", encoding="utf-8") as stream:
        writer = csv.writer(stream)
        bases = [3,4,5,8,9,16]
        writer.writerow(["n"] + [f"a_b{b}" for b in bases])
        for n in range(101):
            writer.writerow([n]+[coefficient_count(b,2*n) for b in bases])


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quick", action="store_true", help="run smaller dense and random checks")
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    args.output.mkdir(parents=True,exist_ok=True)
    report = run_checks(args.quick)
    write_data(args.output / "data")
    (args.output / "verification.json").write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8")
    print(json.dumps(report,indent=2))


if __name__ == "__main__":
    main()
