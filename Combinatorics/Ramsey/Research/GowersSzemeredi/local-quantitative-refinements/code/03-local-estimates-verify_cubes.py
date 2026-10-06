#!/usr/bin/env python3
"""Independent checks of the fourth-order cube expansion.

Standard-library only; no numerical package is required.

1. Enumerate all four-vertex supports for dimensions 2 through 5.
   Determine the gcd of all maximal minors of the reflected matrix.
   The gcd is 0, 1, or 2: parallelogram, independent, or tetrahedral.
   Any three distinct cube vertices have a unimodular affine minor,
   so this determines their Smith invariant factors completely.
2. Compute every coefficient of Q_d(delta + t f) directly from cube
   averages using exact Fraction arithmetic, for several odd/even
   cyclic groups and d=2,3.  Verify coefficients 1,2,3 vanish and
   coefficient 4 is R_d*E(f)+T_d*E_(2)(f).
3. Check the full polynomial on Z/2Z for d=3.
4. Check the full cosine polynomial on Z/3Z for d=3, including the
   nonzero fifth-order term used to establish remainder sharpness.

The program checks finite cases of proved statements; it is not a proof
of the arbitrary-dimension results.
"""

from fractions import Fraction
from itertools import combinations, product
from math import comb, gcd


def det3(a):
    return (a[0][0] * (a[1][1] * a[2][2] - a[1][2] * a[2][1])
            - a[0][1] * (a[1][0] * a[2][2] - a[1][2] * a[2][0])
            + a[0][2] * (a[1][0] * a[2][1] - a[1][1] * a[2][0]))


def constants(d):
    m = 2 ** d
    r = (6 ** d - 2 * 4 ** d + 2 ** d) // 8
    t = (8 ** d - 3 * 6 ** d + 3 * 4 ** d - 2 ** d) // 24
    assert r + t == m * (m - 1) * (m - 2) // 24
    return r, t


def classify_supports(d):
    counts = {0: 0, 1: 0, 2: 0}
    for s in combinations(range(2 ** d), 4):
        # Reflection by the first vertex is an integer affine cube
        # automorphism.  After subtracting its row, only this 3xd
        # binary matrix remains in the maximal affine minors.
        rows = [[((v ^ s[0]) >> i) & 1 for i in range(d)] for v in s[1:]]
        divisor = 0
        for cols in combinations(range(d), 3):
            determinant = det3([[row[c] for c in cols] for row in rows])
            assert abs(determinant) <= 2
            divisor = gcd(divisor, abs(determinant))
        assert divisor in counts
        counts[divisor] += 1

        # A separate bit-parity classifier checks the same result.
        xor = s[0] ^ s[1] ^ s[2] ^ s[3]
        if xor:
            assert divisor == 1
        else:
            categories = {
                tuple(row[i] for row in rows)
                for i in range(d)
            } - {(0, 0, 0)}
            assert categories <= {(1, 1, 0), (1, 0, 1), (0, 1, 1)}
            assert divisor == (0 if len(categories) == 2 else 2)
    r, t = constants(d)
    assert counts[0] == r
    assert counts[2] == t
    assert counts[1] == comb(2 ** d, 4) - r - t
    return counts


def cube_polynomial(f, d):
    """Coefficients E[e_j(f(L_v))], so mean weight is symbolic delta."""
    n = len(f)
    m = 2 ** d
    totals = [Fraction(0) for _ in range(m + 1)]
    for xh in product(range(n), repeat=d + 1):
        x, hs = xh[0], xh[1:]
        coefficients = [Fraction(1)] + [Fraction(0) for _ in range(m)]
        used = 0
        for v in range(m):
            value = f[(x + sum(hs[i] for i in range(d) if (v >> i) & 1)) % n]
            used += 1
            for j in range(used, 0, -1):
                coefficients[j] += value * coefficients[j - 1]
        totals = [a + b for a, b in zip(totals, coefficients)]
    return [a / n ** (d + 1) for a in totals]


def additive_energy(f):
    n = len(f)
    return sum(
        f[x] * f[(x + a) % n] * f[(x + b) % n] * f[(x + a + b) % n]
        for x, a, b in product(range(n), repeat=3)
    ) / n ** 3


def quotient_energy(f):
    # A cyclic group has one nontrivial order-2 character when n is even.
    n = len(f)
    if n % 2:
        return Fraction(0)
    fourier = sum(value * ((-1) ** x) for x, value in enumerate(f)) / n
    return fourier ** 4


def verify_polynomials():
    cases = {
        2: [1, -1],
        3: [2, -1, -1],
        4: [2, -2, 1, -1],
        5: [3, -2, 1, -3, 1],
        6: [3, 1, -2, -3, 2, -1],
    }
    for n, raw in cases.items():
        f = [Fraction(v, 4) for v in raw]
        assert sum(f) == 0
        e, e2 = additive_energy(f), quotient_energy(f)
        for d in (2, 3):
            coefficients = cube_polynomial(f, d)
            r, t = constants(d)
            assert coefficients[0] == 1
            assert coefficients[1:4] == [0, 0, 0]
            assert coefficients[4] == r * e + t * e2
            print(f"Z/{n}Z, d={d}: c4={coefficients[4]}, "
                  f"E={e}, E_(2)={e2}; PASS")
    parity = cube_polynomial([Fraction(1), Fraction(-1)], 3)
    assert parity == [1, 0, 0, 0, 14, 0, 0, 0, 1]
    print("Z/2Z parity polynomial: delta^8 + 14 delta^4 t^4 + t^8; PASS")
    cosine = cube_polynomial([Fraction(1), Fraction(-1, 2), Fraction(-1, 2)], 3)
    assert cosine == [1, 0, 0, 0, Fraction(3, 2), Fraction(1, 2),
                      Fraction(1, 2), 0, Fraction(1, 32)]
    print("Z/3Z cosine polynomial: delta^8 + (3/2)delta^4 t^4 "
          "+ (1/2)delta^3 t^5 + (1/2)delta^2 t^6 + t^8/32; PASS")


def main():
    for d in range(2, 6):
        counts = classify_supports(d)
        print(f"d={d}: parallelograms={counts[0]}, tetrahedra={counts[2]}, "
              f"independent={counts[1]}; PASS")
    verify_polynomials()
    print("All exact finite checks passed.")


if __name__ == "__main__":
    main()
