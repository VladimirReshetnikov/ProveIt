#!/usr/bin/env python3
"""Exclude a five-root disk of depth > kappa(p,5) for the five residual CM orders.

Uses exact integer arithmetic and the class polynomials in the same directory.
For each p dividing the polynomial discriminant it counts ordered pairs (i,j),
i != j, for which v_p(alpha_j/alpha_i - 1) > kappa(p,5). Five roots in one
disk would give at least 20 such pairs, including for a center in an extension
of Q_p or a center with nonzero valuation. At any other p there are no pairs:
integrality and positive relative depth imply v_p(alpha_j - alpha_i) > 0,
forcing positive valuation of the discriminant.
"""
from fractions import Fraction
from math import factorial
import json
from pathlib import Path


def exact_quotient(a, b):
    quotient, remainder = divmod(a, b)
    if remainder:
        raise ArithmeticError('Non-exact division')
    return quotient


def determinant(matrix):
    """Fraction-free elimination with row pivoting."""
    rows = [list(row) for row in matrix]
    n = len(rows)
    previous, sign = 1, 1
    for k in range(n - 1):
        pivot_row = next((i for i in range(k, n) if rows[i][k]), None)
        if pivot_row is None:
            return 0
        if pivot_row != k:
            rows[k], rows[pivot_row] = rows[pivot_row], rows[k]
            sign = -sign
        pivot = rows[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                numerator = pivot * rows[i][j] - rows[i][k] * rows[k][j]
                rows[i][j] = exact_quotient(numerator, previous)
            rows[i][k] = 0
        previous = pivot
    return sign * rows[-1][-1]


def algebra_norm(H, g):
    """Determinant of multiplication by g in Q[X]/H; deg(g) <= deg(H)."""
    h = len(H) - 1
    assert H[-1] == 1 and len(g) <= h + 1
    g = list(g) + [0] * (h + 1 - len(g))
    column = [g[i] - g[h] * H[i] for i in range(h)]
    columns = []
    for _ in range(h):
        columns.append(column)
        high = column[-1]
        column = [a - high * c for a, c in zip([0] + column[:-1], H)]
    return determinant(columns)  # transpose of the multiplication matrix


def interpolate_integers(values):
    """Newton's forward formula, in the ordinary monomial basis."""
    n = len(values) - 1
    coefficients = [0] * (n + 1)
    falling = [1]
    differences = values
    for k in range(n + 1):
        scale = exact_quotient(differences[0], factorial(k))
        for i, a in enumerate(falling):
            coefficients[i] += scale * a
        # Multiply Y(Y-1)...(Y-k+1) by (Y-k).
        falling = [a - k*b for a, b in zip([0] + falling, falling + [0])]
        differences = [b - a for a, b in zip(differences, differences[1:])]
    return coefficients


def distinct_prime_factors(n):
    if n <= 0:
        raise ValueError('Positive nonzero discriminant magnitude required')
    p = 2
    while p*p <= n:
        if n % p == 0:
            yield p
            while n % p == 0:
                n //= p
        p = 3 if p == 2 else p + 2
    if n > 1:
        yield n


def ratio_polynomial(H):
    """Return R(Y)/Y^h, where R is the norm of H((1+Y)X)."""
    h = len(H) - 1
    def evaluate(y):
        return algebra_norm(H, [a*(1+y)**i for i, a in enumerate(H)])
    coefficients = interpolate_integers([evaluate(y) for y in range(h*h + 1)])
    assert coefficients[:h] == [0]*h and coefficients[h]
    assert coefficients[-1] == ((-1)**h * H[0])**h
    # An additional evaluation checks conversion to the monomial basis.
    assert sum(a*(-1)**i for i, a in enumerate(coefficients)) == H[0]**h
    return coefficients[h:]


def valuation(n, p):
    assert n
    exponent = 0
    while n % p == 0:
        n //= p
        exponent += 1
    return exponent


def close_ordered_pairs(R, p):
    depth = Fraction(2 if p == 2 else 1, 1 if p <= 3 else p - 4)
    # A root directly on the boundary is excluded by breaking ties toward
    # the least index. This is the strict-disk form of the Newton polygon.
    return min((valuation(a,p) + i*depth, i) for i, a in enumerate(R) if a)[1]


def main():
    directory = Path(__file__).resolve().parent
    polynomials = json.loads((directory/'cm-extended-polys.json').read_text())
    polynomials['131'] = json.loads((directory/'cm-all-polys.json').read_text())['131']
    for D in (87, 131, 348, 432, 675):
        H = polynomials[str(D)]
        h = len(H) - 1
        derivative = [i*H[i] for i in range(1,h+1)]
        disc = (-1)**(h*(h-1)//2) * algebra_norm(H, derivative)
        R = ratio_polynomial(H)
        assert R[0] == (-1)**(h + h*(h-1)//2) * H[0] * disc
        counts = [(p,close_ordered_pairs(R,p)) for p in distinct_prime_factors(abs(disc))]
        maximum = max(count for p,count in counts)
        if maximum >= 20:
            raise ArithmeticError(f'Pair bound does not exclude a five-root disk for -{D}')
        maximizers = ','.join(str(p) for p,count in counts if count == maximum)
        print(f'D={D} discriminant_primes={len(counts)} max_pairs={maximum} at_p={maximizers}')
    print('All five orders exclude five roots in a disk of depth > kappa(p,5).')


if __name__ == '__main__':
    main()
