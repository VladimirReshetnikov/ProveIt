#!/usr/bin/env python3
"""Arithmetic cross-checks for the four-step Cayley-tower theorem. Python 3."""

from collections import Counter
from math import isqrt


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n)+1))


def projective_point_count(p):
    """Count all F_p-points, including zero coordinates, using pair convolution.

    pairs[(s,t)] is the number of ordered (x,y) with x²+y²=s, x⁴+y⁴=t.
    Two ordered pairs give a point on both cones when their moments cancel.
    Remove the affine origin and quotient by the free scalar action.
    """
    square_multiplicity = Counter(x*x % p for x in range(p))
    pairs = Counter()
    for a, ma in square_multiplicity.items():
        for b, mb in square_multiplicity.items():
            pairs[(a+b) % p, (a*a+b*b) % p] += ma*mb
    affine = sum(n*pairs[(-s % p, -t % p)] for (s, t), n in pairs.items())
    points, remainder = divmod(affine-1, p-1)
    assert not remainder
    return points


def reduced_laplacian(p, steps):
    count = p*p-1
    matrix = [[0]*count for _ in range(count)]
    for i in range(count):
        x, y = divmod(i, p)
        matrix[i][i] = 2*len(steps)
        for dx, dy in steps:
            for sign in (-1, 1):
                j = ((x+sign*dx) % p)*p + (y+sign*dy) % p
                if j < count:
                    matrix[i][j] -= 1
    return matrix


def smith_exponents(matrix, p, precision):
    """Elementary divisor exponents if they are all strictly below precision.

    Eliminate a unit pivot using invertible row and column operations modulo
    p^precision. If none exists, divide the entire residual matrix by p,
    recording the extra factor for each remaining invariant factor.
    """
    modulus = p**precision
    remaining = [[a % modulus for a in row] for row in matrix]
    exponents = Counter()
    depth = 0
    while remaining:
        pivot = next(((i, j) for i, row in enumerate(remaining)
                      for j, x in enumerate(row) if x % p), None)
        if pivot is None:
            if depth == precision-1:
                raise ArithmeticError("increase precision")
            remaining = [[a//p for a in row] for row in remaining]
            modulus //= p
            depth += 1
            continue
        i, j = pivot
        row = remaining.pop(i)
        unit_inverse = pow(row.pop(j), -1, modulus)
        for other in remaining:
            scalar = (other.pop(j)*unit_inverse) % modulus
            if scalar:
                for k, value in enumerate(row):
                    other[k] = (other[k]-scalar*value) % modulus
        exponents[depth] += 1
    return exponents


def main():
    primes = [p for p in range(11, 323) if prime(p)]
    counts = {p: projective_point_count(p) for p in primes}
    exceptions = [p for p, n in counts.items() if n == 0]
    assert exceptions == [11, 23, 29, 47, 53, 83, 149]
    assert all((n-(p+1))**2 <= 324*p for p, n in counts.items())
    print(f"Exact projective curve point counts at {len(primes)} primes:")
    for p, n in counts.items():
        print(f"  p={p}, #C(F_p)={n}")
    print("Primes with zero points:", exceptions)
    # A direct cofactor computation uses no directional moments.
    for p, a, b, expected in [(11, 1, 3, 46), (13, 3, 4, 62)]:
        steps = [(1, 0), (0, 1), (a, b), (b, -a)]
        matrix = reduced_laplacian(p, steps)
        multiplicities = smith_exponents(matrix, p, precision=8)
        actual = sum(e*count for e, count in multiplicities.items())
        assert sum(multiplicities.values()) == len(matrix)
        assert actual == expected
        print(f"p={p}, steps={steps}, cofactor size={len(matrix)}, "
              f"elementary-divisor exponent counts={dict(multiplicities)}, "
              f"v_p(det)={actual}")
    print("PASS")


if __name__ == "__main__":
    main()
