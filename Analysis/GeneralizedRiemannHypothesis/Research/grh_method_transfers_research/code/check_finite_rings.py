#!/usr/bin/env python3
"""Independent finite checks for the square-zero coefficient ring theorems.

Run with Python 3.10+ using only its standard library. Binary integers encode
polynomials over F_2 by their coefficient bits. In the local checks an integer
encodes three base-p coefficients, giving an element of F_p[x]/(x^3).
"""

from fractions import Fraction
from functools import reduce
from itertools import product


def binary_remainder(a, d):
    while a and a.bit_length() >= d.bit_length():
        a ^= d << (a.bit_length() - d.bit_length())
    return a


def binary_gcd(a, b):
    while b:
        a, b = b, binary_remainder(a, b)
    return a


def binary_squarefree(a):
    # The formal derivative has coefficient a_i at x^(i-1) for odd i.
    derivative = sum(((a >> i) & 1) << (i - 1)
                     for i in range(1, a.bit_length(), 2))
    return a != 0 and binary_gcd(a, derivative) == 1


def check_even_balls():
    print("Exact counts over F_2 (dimension, cutoff, admissible, ball size)")
    for dimension in (1, 2, 3):
        size = 2**dimension
        for n in range(2, 6):
            polys = range(2**(n + 1))
            count = sum(binary_squarefree(reduce(binary_gcd, f)) for f in
                        product(polys, repeat=dimension))
            predicted = size**(n + 1) - 2*size**(n - 1) + 1
            assert count == predicted
            print(dimension, n, count, size**(n + 1))


def check_local(prime, dimension):
    # Enumerate all products r^2 h with scalar(r) in (x). Independently
    # compare membership with the prime-valuation criterion modulo x^3.
    modulus_size = prime**3
    residues = range(modulus_size)
    digits = [[(a // prime**i) % prime for i in range(3)] for a in residues]
    add = [[sum((digits[a][i] + digits[b][i]) % prime * prime**i
                for i in range(3)) for b in residues] for a in residues]
    mul = [[sum(sum(digits[a][j]*digits[b][i - j] for j in range(i + 1))
                % prime * prime**i for i in range(3)) for b in residues]
           for a in residues]

    def ring_product(f, g):
        return (mul[f[0]][g[0]],) + tuple(
            add[mul[f[0]][v]][mul[g[0]][u]]
            for u, v in zip(f[1:], g[1:]))

    ring = list(product(residues, repeat=dimension))
    squares = {ring_product(r, r) for r in ring if r[0] % prime == 0}
    actual = {ring_product(square, h) for square in squares for h in ring}
    if prime == 2:
        expected = {f for f in ring if all(v % prime**2 == 0 for v in f)}
        probability = Fraction(1, prime**(2*dimension))
    else:
        expected = {f for f in ring if
                    (f[0] != 0 and f[0] % prime**2 == 0
                     and all(v % prime == 0 for v in f[1:]))
                    or (f[0] == 0 and all(v % prime**2 == 0 for v in f[1:]))}
        z = Fraction(1, prime)
        probability = z**(dimension+1) - z**(dimension+2) + z**(2*dimension+1)
    assert actual == expected
    assert Fraction(len(actual), len(ring)) == probability
    print("Local square multiples:", prime, dimension, len(actual), "/",
          len(ring), "=", probability)


def check_chain_packing():
    print("Scalar x chain packing (dimension, cutoff, disjoint triples)")
    for dimension in (1, 2, 3):
        n = 4
        size = 2**dimension
        bound = 2**(n - 1)
        used = set()
        count = 0
        for g in product(range(bound), repeat=dimension):
            if not any(g):
                continue
            power = min((u & -u).bit_length() - 1 for u in g if u)
            if power % 3:
                continue
            for j in range(3):
                term = tuple(u << j for u in g)
                assert max(term) < 2**(n + 1) and term not in used
                used.add(term)
            count += 1
        predicted = sum(size**(n-1-3*j) - size**(n-2-3*j)
                        for j in range((n-2)//3+1))
        assert count == predicted
        print(dimension, n, count)



def check_pair_extremum():
    # Test the injection collisions and the squarefree-core count used to
    # assemble one infinite set at a sequence of finite cutoffs.
    n = 4
    for dimension in (1, 2, 3):
        tails = {}
        for f in product(range(2**(n+1)), repeat=dimension):
            if not any(f):
                continue
            degree = max(f).bit_length()-1
            shift = 2*((n-degree)//2)
            image = tuple(u << shift for u in f)
            if image in tails:
                g = tails[image]
                if max(g) > max(f):
                    smaller, larger = f, g
                else:
                    smaller, larger = g, f
                gap = max(larger).bit_length()-max(smaller).bit_length()
                assert gap > 0 and gap % 2 == 0
                assert tuple(a << gap for a in smaller) == larger
            tails[image] = f
        size = 2**dimension
        assert len(tails) == size**(n+1)-size**(n-1)

    size = 4  # F_2 dual numbers
    def squarefree_ball(n):
        if n < 0:
            return 0
        if n < 2:
            return size**(n+1)-1
        return size**(n+1)-2*size**(n-1)+1

    def squarefree_layer(n):
        return squarefree_ball(n) - squarefree_ball(n-1)

    prev, retained = -1, 0
    print("Pair-avoiding block set over F_2 dual numbers (cutoff, density)")
    for cutoff in [4, 8, 16, 32, 64, 128]:
        for d in (cutoff-1, cutoff):
            retained += sum(squarefree_layer(u)*2**((d-u)//2)
                            for u in range(prev+1,d+1) if (d-u)%2 == 0)
        density = Fraction(retained, size**(cutoff+1))
        target = 1 - Fraction(1, size**2)
        limit = (cutoff-prev)//2
        ratio = Fraction(2, size**2)
        assert target-ratio**limit/(1-ratio) <= density <= target
        print(cutoff, format(float(density), ".12f"))
        prev = cutoff



def check_linear_stars():
    size, n = 4, 5
    seen = set()
    centers = 0
    for g in product(range(2**(n-1)), repeat=2):
        content = reduce(binary_gcd, g)
        if not content or not all(binary_remainder(content, p) for p in (2, 3)):
            continue
        center_degree = max(g).bit_length()-1
        branches = [[g]]
        for p in (2, 3):
            pg = tuple((u << 1) ^ (u if p == 3 else 0) for u in g)
            p2g = tuple((u << 1) ^ (u if p == 3 else 0) for u in pg)
            branches.append([pg, p2g])
        vertices = [f for branch in branches for f in branch]
        assert len(set(vertices)) == 5 and not seen.intersection(vertices)
        seen.update(vertices)
        costs = []
        for mask in range(1 << 5):
            if all(mask & branch for branch in (0b00111, 0b11001)):
                costs.append(sum(Fraction(1, size**(max(f).bit_length()-1))
                                 for i, f in enumerate(vertices) if mask & (1 << i)))
        assert min(costs) == Fraction(2, size**(2+center_degree))
        centers += 1
    print("Disjoint linear stars over F_2 dual numbers:", centers,
          "centers,", len(seen), "vertices")


if __name__ == "__main__":
    check_even_balls()
    for p, b in [(2, 2), (2, 3), (3, 2)]:
        check_local(p, b)
    check_chain_packing()
    check_pair_extremum()
    check_linear_stars()
    print("All exact checks passed.")
