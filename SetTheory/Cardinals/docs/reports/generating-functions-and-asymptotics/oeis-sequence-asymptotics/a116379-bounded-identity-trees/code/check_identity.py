#!/usr/bin/env python3
"""Exact finite-cap identity-tree enumeration by two independent recurrences.

a[n] counts rooted, unordered, rigid trees with n vertices and at most d
children at every vertex. The product route groups distinct available child
types by size; the Newton route separately solves the formal functional
equation degree by degree. All arithmetic in both enumerators is integer.
"""
import argparse
import json
from math import comb
from pathlib import Path

DATA = Path(__file__).resolve().parent.parent / "data"


def positive_product(d, N):
    """Use product_m (1 + u*z**m)**a[m], retaining u-degree <= d."""
    if d < 0 or N < 0:
        raise ValueError("d and N must be nonnegative")
    E = [[0] * (N+1) for _ in range(d+1)]
    E[0][0] = 1
    a = [0] * (N+1)
    for n in range(1, N+1):
        a[n] = sum(E[j][n-1] for j in range(d+1))
        # Descending child-count makes every source row belong to the old
        # product. Choosing ell distinct size-n types contributes C(a[n],ell).
        for j in range(d, -1, -1):
            for ell in range(1, min(j, N//n, a[n])+1):
                choices = comb(a[n], ell)
                for k in range(ell*n, N+1):
                    E[j][k] += choices * E[j-ell][k-ell*n]
    return a


def newton_recurrence(d, N):
    """Solve a[n]=[z**(n-1)]sum(e_j), with p_i=I(z**i).

    j*e_j[m] = sum_i (-1)**(i-1) sum_{r>=1} a[r]*e_{j-i}[m-i*r].
    Divisibility by j is checked at every coefficient. This routine neither
    calls the product enumerator nor reads its output.
    """
    if d < 0 or N < 0:
        raise ValueError("d and N must be nonnegative")
    e = [[0] * (N+1) for _ in range(d+1)]
    e[0][0] = 1
    a = [0] * (N+1)
    for m in range(1, N+1):
        a[m] = sum(e[j][m-1] for j in range(d+1))
        for j in range(1, d+1):
            numerator = 0
            for i in range(1, j+1):
                numerator += (-1)**(i-1) * sum(
                    a[r] * e[j-i][m-i*r] for r in range(1, m//i+1))
            quotient, remainder = divmod(numerator, j)
            if remainder:
                raise ArithmeticError(f"Newton nonintegrality at d={d},m={m},j={j}")
            e[j][m] = quotient
    return a


def load_terms(d, N, path=None):
    """Use a bundled coefficient cache when sufficient; otherwise enumerate."""
    path = Path(path) if path else DATA / "identity-checks.json"
    if path.exists():
        records = json.loads(path.read_text())
        row = records.get(str(d))
        if row and len(row["terms"]) > N:
            return row["terms"][:N+1]
    return positive_product(d, N)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--degrees", nargs="+", type=int, default=[2, 3, 4])
    parser.add_argument("--N", type=int, default=400)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    results = {}
    reference_path = DATA / "identity-checks.json"
    reference = json.loads(reference_path.read_text()) if reference_path.exists() else {}
    for d in args.degrees:
        a = positive_product(d, args.N)
        b = newton_recurrence(d, args.N)
        if a != b:
            n = next(i for i, (x, y) in enumerate(zip(a, b)) if x != y)
            raise AssertionError(f"Enumeration routes disagree at d={d}, n={n}")
        if str(d) in reference:
            saved = reference[str(d)]["terms"]
            common = min(len(a), len(saved))
            assert a[:common] == saved[:common], "Bundled counts differ"
        results[str(d)] = {"N": args.N, "both_integer_routes_agree": True, "terms": a}
        print(f"PASS d={d}: both exact routes agree through n={args.N}; first 15={a[1:16]}")
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(results, indent=2) + "\n")


if __name__ == "__main__":
    main()
