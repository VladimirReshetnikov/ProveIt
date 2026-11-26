#!/usr/bin/env python3
"""Enumerate imaginary quadratic fields of exact class-group exponent 5 in a finite range.

Run with Python 3.9+ and no third-party packages. CSV is written to stdout.
Status and the comparison with the published list are written to stderr.
"""

import argparse
import csv
from collections import Counter
from math import gcd, isqrt
import sys


# Elsenhans, Klüners and Nicolae, author-maintained tables at
# https://math.uni-paderborn.de/en/ag/ca/research/exponent/exponent0
PUBLISHED = (
    47, 79, 103, 127, 131, 179, 227, 347, 443, 523, 571, 619, 683,
    691, 739, 787, 947, 1051, 1123, 1723, 1747, 1867, 2203, 2347,
    2683, 12451, 37363,
)


def fundamental_discriminants(limit):
    """Absolute values of negative fundamental discriminants, via squarefreeness."""
    squarefree = bytearray([1]) * (limit + 1)
    for k in range(2, isqrt(limit) + 1):
        for multiple in range(k * k, limit + 1, k * k):
            squarefree[multiple] = 0
    return {
        d for d in range(3, limit + 1)
        if (d % 4 == 3 and squarefree[d]) or
           (d % 4 == 0 and (-d // 4) % 4 in (2, 3) and squarefree[d // 4])
    }


def all_forms(limit):
    """Yield all canonical reduced primitive positive binary forms in range."""
    for a in range(1, isqrt(limit // 3) + 1):
        # Use b >= 0 when |b| = a or when a = c.
        for b in range(1 - a, a + 1):
            for c in range(a + int(b < 0), (limit + b * b) // (4 * a) + 1):
                if gcd(a, gcd(b, c)) == 1:
                    yield a, b, c


def reduces_to_principal(a, b, c):
    """An integral positive definite primitive form is principal iff reduced A=1."""
    while True:
        q = (a - b) // (2 * a)
        c, b = a * q * q + b * q + c, b + 2 * a * q
        if a <= c:
            return a == 1
        a, b, c = c, -b, a


def power_is_principal(form, exponent):
    a, b, c = form
    d = b * b - 4 * a * c
    # Change variables (x,y) -> (x, tx+y) so the first coefficient is
    # coprime to the discriminant. For each prime dividing d, at least one
    # residue for t works (primitivity; when p=2 the middle term is even).
    t = 0
    while gcd(a + b * t + c * t * t, d) != 1:
        t += 1
    a, b = a + b * t + c * t * t, b + 2 * c * t
    if a == 1:
        return True
    parity = d % 2
    constant = (parity * parity - d) // 4
    # omega = (parity + sqrt(d))/2 has f(X)=X^2-parity*X+constant.
    # The ideal (a, omega - root) has norm a and the given norm form.
    root = ((parity - b) // 2) % a
    inverse_derivative = pow(2 * root - parity, -1, a)
    modulus = a
    for _ in range(1, exponent):
        value = root * root - parity * root + constant
        assert value % modulus == 0
        digit = (-(value // modulus) * inverse_derivative) % a
        root += digit * modulus
        modulus *= a
    # The ideal (a^exponent, omega - root) is the desired ideal power:
    # it contains that power by evaluation and they have equal index.
    value = root * root - parity * root + constant
    assert value % modulus == 0
    return reduces_to_principal(modulus, parity - 2 * root, value // modulus)


def is_nontrivial_five_power(h):
    if h <= 1:
        return False
    while h % 5 == 0:
        h //= 5
    return h == 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--limit', type=int, default=250000, help='largest absolute discriminant')
    limit = parser.parse_args().limit
    if limit < 3:
        parser.error('limit must be at least 3')
    fundamental = fundamental_discriminants(limit)
    counts = Counter()
    for a, b, c in all_forms(limit):
        absolute_disc = 4 * a * c - b * b
        if absolute_disc in fundamental:
            counts[absolute_disc] += 1
    assert set(counts) == fundamental
    candidates = {d for d, h in counts.items() if is_nontrivial_five_power(h)}
    initial = len(candidates)
    for a, b, c in all_forms(limit):
        absolute_disc = 4 * a * c - b * b
        if absolute_disc in candidates and not power_is_principal((a, b, c), 5):
            candidates.remove(absolute_disc)
    published_in_range = {d for d in PUBLISHED if d <= limit}
    if candidates != published_in_range:
        raise ValueError(f'difference from published table: {sorted(candidates ^ published_in_range)}')
    out = csv.writer(sys.stdout, lineterminator='\n')
    out.writerow(['fundamental_discriminant', 'class_number', 'class_group_exponent'])
    for d in sorted(candidates):
        out.writerow([-d, counts[d], 5])
    print(f'|D| <= {limit}: {len(counts)} fields, {sum(counts.values())} reduced forms, '
          f'{initial} nontrivial 5-power class numbers, {len(candidates)} exponent-five fields. '
          'All entries agree with the published table.', file=sys.stderr)


if __name__ == '__main__':
    main()
