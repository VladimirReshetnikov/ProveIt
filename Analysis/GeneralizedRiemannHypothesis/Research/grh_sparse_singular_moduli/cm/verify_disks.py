#!/usr/bin/env python3
"""Verify p-adic disk obstructions to sparse multiples from exact coefficients."""
from collections import Counter
from fractions import Fraction
from math import comb, factorial, isqrt
from pathlib import Path
import csv
import json

HERE = Path(__file__).resolve().parent


def valuation(n, p):
    """Called only on nonzero integers."""
    assert n != 0
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def shifted_coefficients(coeff, p, scale, unit):
    """Coefficient list of H(p^scale (unit + Y)), starting with the constant."""
    return [
        sum(coeff[j] * p**(scale*j) * comb(j, i) * unit**(j-i)
            for j in range(i, len(coeff)))
        for i in range(len(coeff))
    ]


def check_row(coeff, t, p, k, a, radius):
    assert t in (4, 5) and 1 < p and all(p % d for d in range(2, isqrt(p)+1))
    assert k >= 0 and a % p != 0
    shifted = shifted_coefficients(coeff, p, k, a)
    # Smallest minimizing index counts the roots strictly inside the disk.
    weights = [(valuation(n, p) + i*radius, i) for i, n in enumerate(shifted) if n]
    count = min(weights)[1]
    assert count >= t
    assert radius > Fraction(1, p-1)
    # Minimum t moments control all later moments by a monic integral recurrence.
    w = lambda n: n*radius - valuation(factorial(n), p)
    B = max(w(i) for i in range(t))
    n = t
    # v_p(n!) <= (n-1)/(p-1) for n>=1 (Legendre). Once this lower
    # bound on w exceeds B, it does so at every larger index as well.
    while n*radius - Fraction(n-1, p-1) <= B:
        assert w(n) > B
        n += 1
    return count


def main():
    polys = json.loads((HERE/"class_polynomials.json").read_text())
    expected = {int(D) for D in polys}
    rows = list(csv.DictReader((HERE/"disk_witnesses.csv").read_text().splitlines()))
    verified = {4: set(), 5: set()}
    counts = Counter()
    for row in rows:
        D, t, p, k, a = [int(row[s]) for s in ("Delta", "terms", "prime", "scale", "unit")]
        r = Fraction(row["lambda"])
        assert D not in verified[t]
        check_row(polys[str(D)], t, p, k, a, r)
        verified[t].add(D)
        counts[t, p] += 1
    assert verified[4] == expected and len(expected) == 79
    assert verified[5] == {int(D) for D, c in polys.items() if len(c) == 6} - {-131}
    for t in (4, 5):
        print(f"{len(verified[t])} discriminants certified against {t}-term multiples")
        print("  prime counts:", dict(sorted((p,n) for (u,p),n in counts.items() if u==t)))


if __name__ == "__main__":
    main()
