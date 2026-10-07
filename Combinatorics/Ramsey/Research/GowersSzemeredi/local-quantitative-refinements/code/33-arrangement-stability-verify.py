#!/usr/bin/env python3
"""Reproduce exact finite checks. These are tests, not proofs of general theorems."""
from __future__ import annotations

from dataclasses import replace
from collections import Counter
from fractions import Fraction as F
from itertools import product
import argparse
import json
from pathlib import Path
from random import Random

from arrangements import (count, decode, defect_lower, error, quadratic_lower,
                          sharp_family_error, verify_model, prime_family_error)

ROOT = Path(__file__).resolve().parents[1]


def table_from(values, n, m):
    return [list(values[x*m:(x+1)*m]) for x in range(n)]


def brute_count(table, q):
    """Independent literal enumeration, for s=4 only."""
    n, m = len(table), len(table[0])
    good = total = 0
    for h, a, b, c in product(range(m), range(n), range(n), range(n)):
        xs = (a, b, c, (a+b-c) % n)
        for ys in product(range(m), repeat=4):
            ds = [(table[x][(y+h) % m]-table[x][y]) % q for x, y in zip(xs, ys)]
            good += (ds[0]+ds[1]-ds[2]-ds[3]) % q == 0
            total += 1
    return good, total


def brute_distance(table, q):
    """Independent enumeration including every row constant; only small inputs."""
    n, m = len(table), len(table[0])
    best = n*m
    for b, c in product(range(q), repeat=2):
        if n*b % q or m*b % q or m*c % q:
            continue
        for aa in product(range(q), repeat=n):
            d = sum(table[x][y] != (aa[x]+(b*x+c)*y) % q
                    for x in range(n) for y in range(m))
            best = min(best, d)
    return F(best, n*m)


def check_table(table, q, brute=False):
    model = decode(table, q)
    assert verify_model(table, q, model)
    delta = model.distance
    if brute:
        assert delta == brute_distance(table, q)
        assert count(table, q, 4) == brute_count(table, q)
    n, m = len(table), len(table[0])
    row_counts = [Counter((table[x][y]-model.value(x,y)) % q for y in range(m))
                  for x in range(n)]
    collision_error = sum((1-sum(F(k*k, m*m) for k in cs.values())
                           for cs in row_counts), F(0))/n
    assert collision_error >= delta
    eps4 = error(table, q, 4)
    assert (delta == 0) == (eps4 == 0)
    for s in (4, 6, 16):
        eps = eps4 if s == 4 else error(table, q, s)
        assert eps4 <= eps <= F(s,4)*eps4
        if delta <= F(1, 4):
            assert eps >= defect_lower(delta, s), (table, q, s, eps, delta)
            if delta:
                assert eps >= (collision_error/delta)*defect_lower(delta, s)
        if delta <= F(1, 2*(s-1)):
            assert eps >= quadratic_lower(delta, s)
        if eps < F(1, 216):
            assert delta <= 6*eps + 36*eps/(1-72*eps)
        if eps <= F(1, 240*(s-1)):
            # Two exact inequalities imply the stated radical bound.
            assert delta <= F(1, 4*(s-1))
            assert quadratic_lower(delta, s) <= eps
    bad_model = replace(model, mismatches=model.mismatches+1)
    assert not verify_model(table, q, bad_model)
    return (delta == 0)


def run(extended=False):
    exhaustive = [(2, 2, 2), (3, 2, 2), (3, 3, 2), (2, 3, 3), (3, 4, 2)]
    if extended:
        exhaustive.append((3, 3, 3))
    rows = []
    for n, m, q in exhaustive:
        exact = 0
        for vals in product(range(q), repeat=n*m):
            exact += check_table(table_from(vals, n, m), q, brute=(n*m <= 6))
        row = {"n": n, "m": m, "q": q, "tables": q**(n*m), "zero_error_tables": exact,
               "orders": [4, 6, 16], "literal_enumeration": n*m <= 6}
        rows.append(row)
        print("PASS", row, flush=True)
    rng = Random(20261006)
    sampled = []
    for n, m, q, amount in [(4, 4, 4, 100), (5, 4, 6, 100), (5, 5, 5, 100)]:
        for _ in range(amount):
            table = [[rng.randrange(q) for _ in range(m)] for _ in range(n)]
            check_table(table, q)
        sampled.append({"n": n, "m": m, "q": q, "tables": amount})
    family = []
    for n in (3, 5, 7, 9, 11):
        table = [[int(x == 0)*y for y in range(2)] for x in range(n)]
        assert decode(table, 2).distance == F(1, 2*n)
        for s in (4, 6, 16):
            assert error(table, 2, s) == sharp_family_error(n, s)
        assert sharp_family_error(n, 4) == defect_lower(F(1, 2*n), 4)
    for n in (101, 2001, 100001):
        delta = F(1, 2*n)
        item = {"n": n, "distance": str(delta), "errors": {}}
        for s in (4, 6, 16):
            eps = sharp_family_error(n, s)
            assert eps >= defect_lower(delta, s)
            if eps <= F(1, 240*(s-1)):
                assert delta <= F(1, 4*(s-1))
                assert eps >= quadratic_lower(delta, s)
            item["errors"][str(s)] = str(eps)
        assert sharp_family_error(n, 4) == defect_lower(delta, 4)
        family.append(item)
    prime_families = []
    for p in (3, 5, 7, 11, 13, 17):
        table = [[int(x == 0)*y for y in range(p)] for x in range(p)]
        assert decode(table, p).distance == F(p-1, p*p)
        entry = {"p": p, "distance": str(F(p-1,p*p)), "errors": {}}
        for s in (4, 6, 16):
            observed = error(table, p, s)
            assert observed == prime_family_error(p, s)
            entry["errors"][str(s)] = str(observed)
        prime_families.append(entry)
    invalid = [([], 2, 4), ([[0], [0, 1]], 2, 4), ([[2]], 2, 4),
               ([[0]], 0, 4), ([[False]], 2, 4), ([[0]], 2, 5), ([[0]], 2, 2)]
    for table, q, s in invalid:
        try:
            count(table, q, s)
        except ValueError:
            pass
        else:
            raise AssertionError(("invalid input accepted", table, q, s))
    # Cubic reversion through order four, exact polynomial coefficients.
    from polynomial_checks import verify_polynomials
    polynomial = verify_polynomials()
    return {"status": "PASS", "arithmetic": "exact Python integers and fractions.Fraction",
            "seed": 20261006, "exhaustive": rows, "sampled": sampled,
            "sharp_families": family, "prime_families": prime_families, "invalid_inputs_rejected": len(invalid),
            "model_score_corruption_rejected_per_table": True,
            "polynomial_checks": polynomial,
            "limitation": "Finite tests and ordinary Python are not kernel-checked proofs."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--extended", action="store_true", help="also exhaust all 3x3 tables over Z_3")
    parser.add_argument("--output", type=Path, default=ROOT / "data" / "verification.json")
    args = parser.parse_args()
    result = run(args.extended)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8")
    print(f"All checks passed; report written to {args.output}")


if __name__ == "__main__":
    main()
