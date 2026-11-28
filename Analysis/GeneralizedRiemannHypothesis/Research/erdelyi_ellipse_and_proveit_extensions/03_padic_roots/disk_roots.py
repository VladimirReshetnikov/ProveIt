"""Exact attainable root counts for sparse univariate polynomials on one p-adic disk.

Usage: python disk_roots.py PRIME COMMA_SEPARATED_EXPONENTS [--depth FRACTION]
Default disk: v_p(x - 1) > 1/(p-1). A given depth uses >=.
Python 3.9+ standard library. Root multiplicities are counted.
"""
from argparse import ArgumentParser
from fractions import Fraction
from itertools import combinations_with_replacement
from math import comb, gcd, isqrt


def digit_sum(n, p):
    total = 0
    while n:
        n, digit = divmod(n, p)
        total += digit
    return total


def modulus(t, p):
    if t == 1:
        return 1
    largest = max(digit_sum(i, p) for i in range(t))
    return p ** ((largest - 1 + p - 2) // (p - 1))


def least_lift(residues, q):
    counts = {}
    values = []
    for residue in residues:
        n = counts.get(residue, 0)
        values.append(residue + n * q)
        counts[residue] = n + 1
    return sorted(values)


def valuation(n, p):
    if n == 0:
        raise ValueError("valuation requires a nonzero integer")
    n = abs(n)
    power = 0
    while n % p == 0:
        n //= p
        power += 1
    return power


def primitive(coeff):
    common = 0
    for a in coeff:
        common = gcd(common, a)
    return [a // common for a in coeff] if common else coeff


def counts(p, exponents, depth=None, compress=True):
    """Return all possible root counts. Use compress=False to test original exponents."""
    if p < 2 or any(p % d == 0 for d in range(2, isqrt(p) + 1)):
        raise ValueError("p must be a prime")
    E = sorted(exponents)
    if not E or E[0] < 0 or len(E) != len(set(E)):
        raise ValueError("supply a nonempty set of distinct nonnegative exponents")
    threshold = Fraction(1, p - 1)
    if depth is not None and Fraction(depth) <= threshold:
        raise ValueError("the closed disk depth must exceed 1/(p-1)")
    r = threshold if depth is None else Fraction(depth)
    sign = 1 if depth is None else -1
    if compress:
        q = modulus(len(E), p)
        E = least_lift([v % q for v in E], q)
    width = E[-1] + 1
    echelon = []
    for n in E:
        coeff = [comb(n, k) if k <= n else 0 for k in range(width)]
        for pivot, previous in echelon:
            if coeff[pivot]:
                a, b = previous[pivot], coeff[pivot]
                coeff = primitive([a * x - b * y for x, y in zip(coeff, previous)])
        indices = (k for k, a in enumerate(coeff) if a)
        pivot = min(indices, key=lambda k: (
            r.denominator * valuation(coeff[k], p) + r.numerator * k, sign * k))
        echelon.append((pivot, coeff))
    return sorted(k for k, _ in echelon)


def envelope(p, t, depth=None):
    q = modulus(t, p)
    maximum = -1
    example = None
    for profile in combinations_with_replacement(range(q), t):
        E = least_lift(profile, q)
        current = counts(p, E, depth, compress=False)[-1]
        if current > maximum:
            maximum, example = current, E
    return maximum, example


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("prime", type=int)
    parser.add_argument("exponents", help="example: 0,1,5,10,15")
    parser.add_argument("--depth", type=Fraction)
    args = parser.parse_args()
    print(counts(args.prime, [int(k) for k in args.exponents.split(",")], args.depth))
