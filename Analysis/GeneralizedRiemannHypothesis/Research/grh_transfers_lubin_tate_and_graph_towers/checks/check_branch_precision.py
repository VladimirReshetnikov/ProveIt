#!/usr/bin/env python3
"""Exact tests of Lubin--Tate branch precision; Python 3.8+, standard library.

Primary calculation: multiply X in a monic polynomial quotient over Z/p^r.
Independent calculation, when q=p: use the literal multiplicative branches
(1+X)^b-1 in a different coordinate and invert their product in Laurent series.
All polynomial coefficient lists start with the constant coefficient.
"""
from itertools import combinations, combinations_with_replacement
from math import comb
from collections import Counter


def multiply(left, right, modulus, length=None):
    size = len(left) + len(right) - 1
    if length is not None:
        size = min(size, length)
    out = [0] * size
    for i, a in enumerate(left[:size]):
        if a:
            for j, b in enumerate(right[:size-i]):
                out[i+j] += a*b
    return [x % modulus for x in out]


def poly_power(base, exponent, modulus):
    result = [1]
    for _ in range(exponent):
        result = multiply(result, base, modulus)
    return result


def division_iterates(p, q, precision, depth):
    modulus = p**precision
    levels = [[0, 1]]                       # F_0 = X
    for _ in range(depth):
        prev = levels[-1]
        nxt = poly_power(prev, q, modulus)
        for i, c in enumerate(prev):
            nxt[i] = (nxt[i] + p*c) % modulus
        levels.append(nxt)
    return levels


def companion_threshold(p, q, precision, contacts):
    """First t with X^t=0 mod (p^r, product F_v). Unramified coefficients."""
    if not contacts:
        return 0
    modulus = p**precision
    levels = division_iterates(p, q, precision, max(contacts))
    poly = [1]
    for depth in contacts:
        poly = multiply(poly, levels[depth], modulus)
    degree = len(poly)-1
    assert degree == sum(q**v for v in contacts) and poly[-1] == 1
    # X^degree belongs to p times the quotient, so this coarse bound
    # terminates independently of the bound being tested.
    remainder = [1] + [0]*(degree-1)
    for t in range(degree*precision+1):
        if not any(remainder):
            return t
        high = remainder[-1]
        remainder = [(a-high*b) % modulus
                     for a, b in zip([0]+remainder[:-1], poly)]
    raise ArithmeticError("expected a nilpotent residue of X")


def inverse_series(poly, length, modulus):
    result = [pow(poly[0], -1, modulus)]
    for i in range(1, length):
        s = sum(poly[j]*result[i-j] for j in range(1, min(i+1, len(poly))))
        result.append((-result[0]*s) % modulus)
    return result


def literal_branch_threshold(p, precision, points, distinguished):
    """Compute the actual pole of the Laurent inverse using raw branch series.

    Split Delta = X^w U + L, deg L < w and L=0 modulo p.  X^(rw)/Delta
    equals sum_{j<r} X^((r-j-1)w) (-L)^j U^(-j-1) modulo p^r.  Its
    lowest nonzero coefficient occurs by degree rw; the finite expansion
    thus measures the pole directly, without using the factorization into F_v.
    """
    modulus = p**precision
    d = [1]
    for c in points:
        if c == distinguished:
            continue
        branch_difference = [
            ((comb(distinguished, i) if i <= distinguished else 0)
             - (comb(c, i) if i <= c else 0)) % modulus
            for i in range(max(c, distinguished)+1)
        ]
        d = multiply(d, branch_difference, modulus)
    w = next(i for i, a in enumerate(d) if a % p)
    length = precision*w+1
    u_inverse = inverse_series(d[w:], length, modulus)
    negative_l = [(-a) % modulus for a in d[:w]]
    if not w:
        return 0
    term = u_inverse
    multiplier = multiply(negative_l, u_inverse, modulus, length)
    result = [0]*length
    for j in range(precision):
        shift = (precision-j-1)*w
        for i, a in enumerate(term[:length-shift]):
            result[shift+i] = (result[shift+i]+a) % modulus
        term = multiply(term, multiplier, modulus, length)
    first = next(i for i, a in enumerate(result) if a)
    return length-1-first


def valuation(n, p):
    assert n
    n = abs(n)
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def test_profile(p, q, precision, contacts):
    actual = companion_threshold(p, q, precision, contacts)
    omega = sum(q**v for v in contacts)
    depth = max(contacts, default=0)
    if not depth:
        assert actual == omega
        return actual
    m = contacts.count(depth)
    slope = (q-1)*q**(depth-1)
    upper = omega+(precision-1)*slope
    assert precision*slope <= actual <= upper
    assert (actual == upper) == (comb(m+precision-2, precision-1) % p != 0)
    if depth == 1:
        last = max(j for j in range(precision)
                   if j+valuation(comb(m+j-1, j), p) < precision)
        assert actual == omega+(q-1)*last
    return actual


def main():
    counts = Counter()
    for p, q, max_depth in [(2, 2, 3), (2, 4, 2), (3, 3, 2), (5, 5, 2)]:
        for k in range(5):
            for contacts in combinations_with_replacement(range(max_depth+1), k):
                for r in range(1, 9):
                    test_profile(p, q, r, contacts)
                    counts["canonical polynomial cases"] += 1
    # The independent coordinate directly uses integer directions in Q_p.
    # Repeated isomorphism types of pointed configurations are intentional.
    for p, pool in [(2, [0, 1, 2, 4, 6]), (3, [0, 1, 3, 6, 9])]:
        for size in range(1, len(pool)+1):
            for points in combinations(pool, size):
                for b in points:
                    contacts = [valuation(b-c, p) for c in points if c != b]
                    for r in [1, 2, 3, 4]:
                        canonical = companion_threshold(p, p, r, contacts)
                        other_coordinate = literal_branch_threshold(p, r, points, b)
                        assert canonical == other_coordinate, (p, r, points, b)
                        counts["literal multiplicative-branch comparisons"] += 1
    for label, n in counts.items():
        print(f"{label}: {n}")
    print("example pole orders t(r), r=1,...,8")
    for p, q, contacts in [(3, 3, [2]), (2, 2, [1, 1]), (3, 3, [1, 1, 1]),
                           (2, 4, [0, 1, 2, 2]), (3, 3, [0, 1, 2, 2, 2])]:
        values = [companion_threshold(p, q, r, contacts) for r in range(1, 9)]
        print(f"  p={p}, q={q}, contacts={contacts}: {values}")
    print("PASS")


if __name__ == "__main__":
    main()
