#!/usr/bin/env python3
"""Exact coefficient-matrix checks of the full finite-jet rank theorem.

Logarithms in exponential weights are replaced by rational parameters; the
coefficient-algebra theorem holds for every such specialization.  Additional
cases use genuinely nilpotent and resonant prime weights.  Requires only the
standard library and the companion verify_ranks.py.
"""

import argparse
from fractions import Fraction
import json
from math import factorial
from pathlib import Path

from verify_ranks import RationalRows, prime_factors, totient, unit_row


def multiply(a, b):
    size = len(a)
    return [sum((a[i] * b[j - i] for i in range(j + 1)), Fraction(0))
            for j in range(size)]


def divisor_weight(d, weights, order):
    result = [Fraction(1)] + [Fraction(0)] * order
    for p in prime_factors(d):
        while d % p == 0:
            result = multiply(result, weights[p])
            d //= p
    return result


def jet_rows(q, d, polynomial):
    order = len(polynomial) - 1
    columns = q * (order + 1)
    for r in range(q // d):
        target = (d * r) % q
        for j in range(order + 1):
            row = [Fraction(0)] * columns
            for lift in range(d):
                row[j * q + r + lift * (q // d)] += 1
            for ell in range(j + 1):
                row[(j - ell) * q + target] -= polynomial[ell]
            yield row


def check_case(q, order, name, weights):
    columns = (order + 1) * q
    space = RationalRows(columns)
    for p in prime_factors(q):
        for row in jet_rows(q, p, weights[p]):
            space.add(row)
    prime_rank = space.rank
    for d in range(2, q + 1):
        if q % d == 0:
            wd = divisor_weight(d, weights, order)
            for row in jet_rows(q, d, wd):
                space.add(row)
    assert space.rank == prime_rank, (q, order, name, "prime sufficiency")
    free_dimension = columns - space.rank
    assert free_dimension == (order + 1) * totient(q)
    for j in range(order + 1):
        assert space.add(unit_row(columns, j * q)), (q, order, name, "endpoint")
    pinned_dimension = columns - space.rank
    assert pinned_dimension == (order + 1) * (totient(q) - 1)
    return {
        "q": q,
        "maximum_jet_order": order,
        "weight_system": name,
        "unprescribed_endpoint_dimension": free_dimension,
        "all_endpoints_prescribed_dimension": pinned_dimension,
        "prime_and_all_divisor_ranks_agree": True,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("data/jet_rank_checks.json"))
    args = parser.parse_args()
    records = []
    for q in (1, 2, 3, 4, 6, 8, 12, 15, 20, 30):
        for order in range(4):
            for s in (-2, 0, 2):
                weights = {
                    p: [Fraction(p) ** s * Fraction(p) ** ell / factorial(ell)
                        for ell in range(order + 1)]
                    for p in prime_factors(q)
                }
                records.append(check_case(q, order, f"p^{s} exp(p eta)", weights))
            nilpotent = {
                p: ([Fraction(0)] + [Fraction(1)] + [Fraction(0)] * order)[:order + 1]
                if p == 2 else [Fraction(1)] + [Fraction(0)] * order
                for p in prime_factors(q)
            }
            records.append(check_case(q, order, "w_2=eta; odd-prime weights=1", nilpotent))
    payload = {
        "description": "Exact formal finite-jet rank checks, including nilpotent coefficient weights.",
        "arithmetic": "fractions.Fraction",
        "case_count": len(records),
        "all_assertions_passed": True,
        "cases": records,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in payload.items() if key != "cases"}, indent=2))


if __name__ == "__main__":
    main()
