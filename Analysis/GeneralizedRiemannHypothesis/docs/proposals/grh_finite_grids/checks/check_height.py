#!/usr/bin/env python3
"""Exact projective reduction checks in O = Z[sqrt(-5)] at the ramified place over 2."""
from fractions import Fraction
from itertools import combinations
from math import gcd
import json


def primitive(a, b, c):
    g = gcd(gcd(a, b), c)
    return (a // g, b // g, c // g)


def norm_numerator(x):
    a, b, _ = x
    return a*a + 5*b*b


def denominator_norm(x):
    a, b, c = x
    return c*c // gcd(c, norm_numerator(x))


def height(x):
    a, b, c = x
    return max(c*c, norm_numerator(x)) // gcd(c, norm_numerator(x))


def local_code(x, n):
    """Chart bit and residue mod P^n, where P=(2,1+sqrt(-5))."""
    a, b, c = x
    inverse_chart = c % 2 == 0
    if inverse_chart:
        a, b, c = primitive(c*a, -c*b, norm_numerator(x))
    assert c % 2 == 1
    j, odd = divmod(n, 2)
    base = 2**j
    modulus = base * 2**odd
    inv = pow(c, -1, modulus)
    u, v = a*inv % modulus, b*inv % modulus
    top_parity = ((u//base + v//base) % 2) if odd else 0
    return (inverse_chart, u % base, v % base, top_parity)


def obstruction_norm(x, y):
    a, b, c = x
    d, e, f = y
    aa, bb = a*f - d*c, b*f - e*c
    num = (aa*aa + 5*bb*bb) * denominator_norm(x) * denominator_norm(y)
    den = (c*f)**2
    assert num > 0 and num % den == 0
    return num // den


def main():
    bound = 32
    points = sorted({primitive(a, b, c) for c in range(1, bound+1)
                     for a in range(-bound, bound+1) for b in range(-bound, bound+1)
                     if height(primitive(a, b, c)) <= bound})
    # If H <= B then c <= B and a^2+5b^2 <= B*c <= B^2. The box covers all points.
    example = (1, 1, 2)
    assert denominator_norm(example) == 2 and height(example) == 3
    assert example in points and local_code(example, 3)[0]
    pairs = list(combinations(points, 2))
    norms = [obstruction_norm(x, y) for x, y in pairs]
    for (x, y), nrm in zip(pairs, norms):
        assert nrm <= 4*height(x)*height(y)
    collisions = {}
    for n in range(1, 14):
        labels = {x: local_code(x, n) for x in points}
        matching = [i for i, (x, y) in enumerate(pairs) if labels[x] == labels[y]]
        assert all(norms[i] % (2**n) == 0 for i in matching)
        assert len(set(labels.values())) <= 2**n + 2**(n-1)
        collisions[n] = len(matching)
    counts = {}
    for B in range(1, bound+1):
        subset = [x for x in points if height(x) <= B]
        n = (4*B*B).bit_length()  # 2^n > 4 B^2, including equality at a lower power.
        assert len({local_code(x, n) for x in subset}) == len(subset)
        assert len(subset) <= 2**n + 2**(n-1) <= 12*B*B
        counts[B] = len(subset)
    moment = sum((Fraction(1, height(x)**3) for x in points), Fraction())
    assert moment <= 36  # 3(q+1) 2^d for d=2, q=2.
    print(json.dumps({
        "model": "Q(sqrt(-5)), P=(2,1+sqrt(-5)), q=2, (2)=P^2",
        "nonprincipal_denominator_example": {"x": "(1+sqrt(-5))/2", "N(den)": 2, "H": 3},
        "max_height": bound, "points": len(points), "distinct_pairs": len(pairs),
        "pair_norm_sandwich": "passed for every pair",
        "colliding_pairs_by_precision": collisions,
        "counts_at_sample_heights": {k: counts[k] for k in (1,2,4,8,16,32)},
        "sum_inverse_cubes": str(moment), "all_injectivity_checks": 32,
    }, indent=2))


if __name__ == "__main__":
    main()
