"""Verify disk certificates for the 79 former CM exceptions; no degree cutoff on annihilators."""
import csv
import json
from collections import Counter
from fractions import Fraction
from math import comb
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def threshold(p, k):
    assert k in (4, 5)
    if p == 2:
        return Fraction(2)
    if p == 3:
        return Fraction(1)
    return Fraction(1, p-k+1)


def valuation(n, p):
    assert n
    v = 0
    while n % p == 0:
        v += 1
        n //= p
    return v


def disk_count(coeffs, p, u, a, k):
    """Number of roots satisfying v_p(x/p^u-a)>the threshold; a is a unit."""
    assert a % p and p in (2, 3, 5, 7, 13, 17)
    h = len(coeffs)-1
    weights = []
    radius = threshold(p, k)
    for j in range(h+1):
        shifted = sum(coeffs[i]*p**(i*u)*comb(i, j)*a**(i-j) for i in range(j, h+1))
        if shifted:
            weights.append((valuation(shifted, p) + j*radius, j))
    return min(weights)[1]


def verify():
    polynomials = json.loads((ROOT/'class_polynomials.json').read_text())
    with (ROOT/'disks.csv').open() as source:
        rows = list(csv.DictReader(source))
    assert len(rows) == len(polynomials) == 79
    assert len({r['abs_discriminant'] for r in rows}) == 79
    counts = Counter()
    five = set()
    for row in rows:
        d, h, p, u, a, n, k = map(int, row.values())
        coeffs = polynomials[str(d)]
        assert h == len(coeffs)-1 and coeffs[-1] == 1
        assert disk_count(coeffs, p, u, a, 4) >= 4
        assert disk_count(coeffs, p, u, a, k) == n and n >= k
        counts[p] += 1
        if k == 5:
            five.add(d)
    assert len(five) == 28
    print('79 four-root certificates by prime:', dict(sorted(counts.items())))
    print('Certificates excluding five terms in degree five:', len(five))
    return set(map(int, polynomials))


if __name__ == '__main__':
    verify()
