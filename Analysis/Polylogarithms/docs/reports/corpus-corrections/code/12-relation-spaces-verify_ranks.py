#!/usr/bin/env python3
"""Exact checks of weighted rational-grid distribution presentations.

Only Python's standard library is required.  No numerical special-function
values enter these checks.  Rows include the representative x=0 (the endpoint
value at a=1).  The all-denominator proof is in distribution_ranks.tex.

Example:
    python code/verify_ranks.py --output data/rank_checks.json
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import json
from math import gcd
from pathlib import Path
import platform
from time import perf_counter


class RationalRows:
    """Incremental exact row echelon space, with Fraction coefficients."""

    def __init__(self, columns: int):
        self.columns = columns
        self.pivots: dict[int, list[Fraction]] = {}

    def copy(self) -> "RationalRows":
        other = RationalRows(self.columns)
        other.pivots = self.pivots.copy()  # Stored rows are never changed.
        return other

    def add(self, row: list[Fraction]) -> bool:
        row = row.copy()
        for j in range(self.columns):
            if not row[j]:
                continue
            if j in self.pivots:
                multiple = row[j]
                pivot = self.pivots[j]
                for k in range(j, self.columns):
                    if pivot[k]:
                        row[k] -= multiple * pivot[k]
            else:
                scale = row[j]
                for k in range(j, self.columns):
                    row[k] /= scale
                self.pivots[j] = row
                return True
        return False

    @property
    def rank(self) -> int:
        return len(self.pivots)


def prime_factors(n: int) -> list[int]:
    factors = []
    p = 2
    while p * p <= n:
        if n % p == 0:
            factors.append(p)
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        factors.append(n)
    return factors


def totient(n: int) -> int:
    result = n
    for p in prime_factors(n):
        result = result // p * (p - 1)
    return result


def weight(d: int, prime_weights: dict[int, Fraction]) -> Fraction:
    result = Fraction(1)
    for p in prime_factors(d):
        while d % p == 0:
            result *= prime_weights[p]
            d //= p
    return result


def distribution_rows(q: int, d: int, wd: Fraction):
    """x=d*r/q, preimages y=(r+j*q/d)/q, in zero-based columns."""
    for r in range(q // d):
        row = [Fraction(0) for _ in range(q)]
        for j in range(d):
            row[r + j * (q // d)] += 1
        row[(d * r) % q] -= wd
        yield row


def unit_row(q: int, r: int) -> list[Fraction]:
    row = [Fraction(0) for _ in range(q)]
    row[r] = Fraction(1)
    return row


def reflection_rows(q: int, sign: int):
    for r in range(q):
        row = unit_row(q, r)
        row[(-r) % q] += sign
        yield row


def check_case(q: int, label: str, prime_weights: dict[int, Fraction]) -> dict:
    phi = totient(q)
    prime_space = RationalRows(q)
    prime_row_count = 0
    for p in prime_factors(q):
        for row in distribution_rows(q, p, prime_weights[p]):
            prime_space.add(row)
            prime_row_count += 1
    assert prime_space.rank == q - phi, (q, label, "prime rank")

    # Adding every all-divisor row must not enlarge the prime-row span.
    all_space = prime_space.copy()
    all_row_count = 0
    for d in range(2, q + 1):
        if q % d:
            continue
        for row in distribution_rows(q, d, weight(d, prime_weights)):
            all_space.add(row)
            all_row_count += 1
    assert all_space.rank == prime_space.rank, (q, label, "prime sufficiency")

    endpoint_space = all_space.copy()
    assert endpoint_space.add(unit_row(q, 0)), (q, label, "endpoint nonzero")
    assert q - endpoint_space.rank == phi - 1

    reflection_residual = {}
    for sign in (-1, 1):
        reflected = endpoint_space.copy()
        for row in reflection_rows(q, sign):
            reflected.add(row)
        expected = 0 if q <= 2 else phi // 2 - (1 - sign) // 2
        assert q - reflected.rank == expected, (q, label, sign)
        reflection_residual[str(sign)] = q - reflected.rank

    # Independent check of the top-denominator-basis assertion.  Resonant
    # systems may fail here without violating the rank theorem.
    unit_space = all_space.copy()
    for r in range(q):
        if gcd(r, q) == 1:
            unit_space.add(unit_row(q, r))
    nonresonant = all(abs(wp) not in (0, 1) for wp in prime_weights.values())
    if nonresonant:
        assert unit_space.rank == q, (q, label, "unit-symbol basis")

    return {
        "q": q,
        "weight_system": label,
        "prime_weights": {str(p): str(wp) for p, wp in prime_weights.items()},
        "phi_q": phi,
        "prime_row_count": prime_row_count,
        "all_divisor_row_count": all_row_count,
        "distribution_rank": all_space.rank,
        "endpoint_quotient_dimension": q - endpoint_space.rank,
        "reflection_quotient_dimensions": reflection_residual,
        "top_unit_symbols_span_quotient": unit_space.rank == q,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-q", type=int, default=48)
    parser.add_argument("--extra-q", default="60,64,72,90,105,120")
    parser.add_argument("--weights", default="-4,-2,-1,0,1,2,3,5")
    parser.add_argument("--output", type=Path, default=Path("data/rank_checks.json"))
    args = parser.parse_args()
    denominators = sorted(set(range(1, args.max_q + 1)) | {
        int(q) for q in args.extra_q.split(",") if q
    })
    powers = [int(s) for s in args.weights.split(",")]
    started = perf_counter()
    records = []
    for q in denominators:
        primes = prime_factors(q)
        for s in powers:
            weights = {p: Fraction(p) ** s for p in primes}
            records.append(check_case(q, f"p^{s}", weights))
        # Includes a zero prime weight and values not arising from a common
        # exponent; these are covered by the stronger weighted theorem.
        custom = {p: Fraction(0 if p == 2 else p - 1) for p in primes}
        records.append(check_case(q, "w_2=0; w_p=p-1 for odd p", custom))
    payload = {
        "description": "Exact rational coefficient-matrix checks; not arithmetic-independence tests.",
        "arithmetic": "Python fractions.Fraction, exact incremental elimination",
        "python_version": platform.python_version(),
        "denominators": denominators,
        "power_exponents": powers,
        "case_count": len(records),
        "all_assertions_passed": True,
        "elapsed_seconds": round(perf_counter() - started, 3),
        "cases": records,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in payload.items() if key != "cases"}, indent=2))


if __name__ == "__main__":
    main()
