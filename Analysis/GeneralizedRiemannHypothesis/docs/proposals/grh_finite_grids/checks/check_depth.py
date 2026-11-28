#!/usr/bin/env python3
"""Exact finite-field rank and Frobenius-relation checks; Python 3.9+, standard library."""
from functools import lru_cache
from math import gcd, lcm

# Lower coefficients, in ascending order, of a monic primitive polynomial.
MODULI = {
    (5, 2): (2, 1),
    (5, 4): (2, 2, 1, 0),
    (5, 6): (2, 1, 0, 0, 0, 0),
    (5, 8): (3, 2, 1, 0, 0, 0, 0, 0),
    (5, 12): (3, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0),
    (3, 8): (2, 0, 0, 1, 0, 0, 0, 0),
}


def primes_dividing(n):
    factor = 2
    while factor * factor <= n:
        if n % factor == 0:
            yield factor
            while n % factor == 0:
                n //= factor
        factor += 1
    if n > 1:
        yield n


class Field:
    def __init__(self, p, degree):
        self.p = p
        self.degree = degree
        self.modulus = MODULI[p, degree]
        self.one = (1,) + (0,) * (degree - 1)
        self.zero = (0,) * degree
        self.generator = (0, 1) + (0,) * (degree - 2)
        self.order = p ** degree
        # Exactly q-1 distinct powers are units, so every nonzero element is a unit.
        n = self.order - 1
        assert self.power(self.generator, n) == self.one
        for ell in primes_dividing(n):
            assert self.power(self.generator, n // ell) != self.one

    @lru_cache(maxsize=8192)
    def multiply(self, a, b):
        d = self.degree
        product = [0] * (2 * d - 1)
        for i, x in enumerate(a):
            for j, y in enumerate(b):
                product[i + j] += x * y
        for i in range(2 * d - 2, d - 1, -1):
            for j, coefficient in enumerate(self.modulus):
                product[i - d + j] -= (product[i] % self.p) * coefficient
        return tuple(x % self.p for x in product[:d])

    @lru_cache(maxsize=8192)
    def power(self, a, n):
        if n == 0:
            return self.one
        half = self.power(a, n // 2)
        square = self.multiply(half, half)
        return self.multiply(square, a) if n % 2 else square

    def subfield_generator(self, size):
        assert (self.order - 1) % (size - 1) == 0
        return self.power(self.generator, (self.order - 1) // (size - 1))


def rank_mod_p(rows, p):
    pivots = {}
    for original in rows:
        row = [x % p for x in original]
        for j in range(len(row)):
            x = row[j]
            if x == 0:
                continue
            if j not in pivots:
                inverse = pow(x, -1, p)
                pivots[j] = [v * inverse % p for v in row]
                break
            row = [(v - x * w) % p for v, w in zip(row, pivots[j])]
    return len(pivots)


def check(p, f, N, r, m):
    # k=2r+m, the first r columns are paired and m are spare.
    P = p ** f
    q = P ** N
    E = Field(p, f * lcm(N, 2 * r))
    b = E.subfield_generator(P ** (2 * r))
    generator_Fq = E.subfield_generator(q)
    weights = [E.power(b, a) for a in range(r)]
    assert len({E.power(b, P ** (2 * i)) for i in range(r)}) == r
    minus_one = tuple(-v % p for v in E.one)
    # Store the complete orbit map on an F_p-basis of its domain.
    # Testing the relations there suffices by additivity of all Frobenius maps.
    rows = []
    for active_col in range(m + 1):
        for active_row in range(r):
            for h in range(f * N):
                y = E.power(generator_Fq, h)
                blocks = []
                for a in range(r):
                    val = y if (active_col == 0 and a == active_row) else E.zero
                    z = [E.multiply(weights[a] if s % 2 == 0 else minus_one,
                                    E.power(val, P ** s)) for s in range(N)]
                    # Clear the nonzero factors in the paired Frobenius relation.
                    for s in range(N):
                        u = weights[a] if s % 2 == 0 else minus_one
                        v = minus_one if s % 2 == 0 else weights[a]
                        assert E.multiply(v, E.power(z[s], P)) == E.multiply(
                            E.power(u, P), z[(s + 1) % N])
                    blocks.extend(z)
                for col in range(1, m + 1):
                    z = [E.multiply(weights[active_row], E.power(y, P ** s))
                         if col == active_col else E.zero for s in range(0, N, 2)]
                    for j, v in enumerate(z):
                        assert E.power(v, P ** (2 * r)) == z[(j + r) % (N // 2)]
                    blocks.extend(z)
                rows.append([coefficient for z in blocks for coefficient in z])
    rank = rank_mod_p(rows, p)
    expected = f * N * r * (m + 1)
    assert rank == expected, (P, N, r, m, rank, expected)
    # Compare the original point space with the grid after the two
    # Vandermonde basis changes. Each list here spans over the prime field.
    grid_rows = []
    offsets = [N] * r + [N // 2] * m
    for block, dimension in enumerate(offsets):
        paired = block < r
        scalar = E.subfield_generator(P) if paired else b
        scalar_degree = f if paired else 2 * r * f
        side = P if paired else P ** 2
        conjugates = [E.power(generator_Fq, side ** j) for j in range(dimension)]
        assert len(set(conjugates)) == dimension
        for basis_index in range(dimension):
            for ell in range(scalar_degree):
                vector = [E.zero] * sum(offsets)
                for j in range(dimension):
                    value = E.multiply(E.power(scalar, ell),
                                       E.power(conjugates[j], basis_index))
                    if paired:
                        value = E.multiply(weights[block] if j % 2 == 0 else minus_one, value)
                    vector[sum(offsets[:block]) + j] = value
                grid_rows.append([value for coordinates in vector for value in coordinates])
    assert rank_mod_p(grid_rows, p) == expected
    assert rank_mod_p(rows + grid_rows, p) == expected
    cost_box = P ** (r * N) * (P ** (2 * r)) ** (m * (N // 2))
    assert cost_box == q ** (r * (m + 1)) == p ** rank
    return rank


def check_specialization():
    # Over F_5, G(U,X)=(U-1)^2*(X^5-U^4*X)^3 vanishes to order >=3
    # at X=U*y for all y in F_5. G(1,X)=0, while its first nonzero
    # (U-1)-coefficient is (X^5-X)^3, with a triple zero at all five points.
    from math import comb
    p = 5
    def shifted_cube(y):
        coeffs = [0] * 16
        for j in range(4):
            exponent = 5 * j + 3 - j
            sign = (-1) ** (3 - j)
            for i in range(exponent + 1):
                coeffs[i] += comb(3, j) * sign * comb(exponent, i) * y ** (exponent - i)
        return [a % p for a in coeffs]
    for y in range(p):
        c = shifted_cube(y)
        assert c[:3] == [0, 0, 0] and c[3] != 0


if __name__ == "__main__":
    # Include r>N/2, m=0, several spare columns, split cycles and a nonprime P.
    cases = [(5, 1, 2, 1, 0), (5, 1, 2, 2, 3), (5, 1, 4, 2, 2),
             (5, 1, 4, 3, 1), (5, 1, 6, 2, 2), (5, 1, 6, 3, 1),
             (5, 1, 2, 4, 1), (3, 2, 2, 2, 2)]
    for p, f, N, r, m in cases:
        rank = check(p, f, N, r, m)
        print(f"P={p**f:2}  N={N}  r={r}  m={m}  gcd(r,N/2)={gcd(r,N//2)}  "
              f"rank over F_{p}={rank}: full rank; cyclic relations and Cartesian grid verified")
    check_specialization()
    print("Hasse-coefficient triple-root example verified at all five points.")
