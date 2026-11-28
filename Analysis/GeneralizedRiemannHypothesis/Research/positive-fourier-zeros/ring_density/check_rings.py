#!/usr/bin/env python3
"""Exhaustive small checks of Lemma 2 and of the disjoint packing.

The two 16-element rings are the h=1, q=2 examples of the paper.
Integers represent coefficients in the basis (1,e0,e1,w).
Polynomial coefficient tuples run from constant to leading coefficient.
"""
from itertools import product


def multiplication_table(diagonal):
    def multiply(a, b):
        answer = (b if a & 1 else 0) ^ (a if b & 1 else 0) ^ (a & b & 1)
        mixed = ((a >> 1) & (b >> 2) & 1) ^ ((a >> 2) & (b >> 1) & 1)
        square = (a >> 2) & (b >> 2) & diagonal
        return answer ^ ((mixed ^ square) << 3)
    return [[multiply(a, b) for b in range(16)] for a in range(16)]


def polynomial_product(a, b, table):
    result = [0] * (len(a) + len(b) - 1)
    for i, coefficient in enumerate(a):
        if coefficient:
            for j, other in enumerate(b):
                result[i + j] ^= table[coefficient][other]
    while result and result[-1] == 0:
        result.pop()
    return tuple(result)


def verify(diagonal):
    table = multiplication_table(diagonal)
    assert all(table[table[a][b]][c] == table[a][table[b][c]]
               for a, b, c in product(range(16), repeat=3))
    lifts = {table[v][v]: v for v in reversed(range(0, 16, 2))}
    squares = sorted(lifts)
    assert squares == ([0, 8] if diagonal else [0])
    n = 3
    # Enumerate every possible square multiplier giving a pair in B_3
    # whose two residues are nonzero and whose ratio has positive residue degree.
    # The scalar part t has degree one. If U=v^2 has degree > 4, then
    # deg(U*bar(f)) >= 6 > deg(t^2*f), since U has only even powers.
    square_multipliers = set()
    for t0 in (0, 1):
        for c0, c2, c4 in product(squares, repeat=3):
            square_multipliers.add((c0 ^ t0, 0, c2 ^ 1, 0, c4))
    pair_count = 0
    for f0, f1 in product(range(16), repeat=2):
        # bar(f) has degree at most 1.
        F0, F1 = f0 & 1, f1 & 1
        if not (F0 or F1):
            continue
        # n=3, d=1 (even n-d) or d=0 (odd n-d).
        allowed = {(c * F1, c * F0) for c in squares}
        for f2, f3 in product(range(0, 16, 2), repeat=2):
            f = (f0, f1, f2, f3)
            for square in square_multipliers:
                if len(polynomial_product(square, f, table)) <= n + 1:
                    assert (f3, f2) in allowed
                    pair_count += 1
    occupied = set()
    triple_count = 0
    for f0, f1 in product(range(1, 16, 2), repeat=2):
        for c, v in lifts.items():
            f = (f0, f1, c, c)
            r = (v, 1, v, c)
            y = polynomial_product(r, f, table)
            z = polynomial_product(r, y, table)
            assert len(y) <= n + 1 and len(z) <= n + 1
            terms = [tuple(poly) + (0,) * (n + 1 - len(poly)) for poly in (f, y, z)]
            assert len(set(terms)) == 3 and not occupied.intersection(terms)
            occupied.update(terms)
            triple_count += 1
    assert 4 * 16**2 * triple_count == len(squares) * 16**(n+1)
    print(f"A_1^{diagonal}: Q=16, s={len(squares)}, {pair_count} square-pair incidences, "
          f"{triple_count} disjoint triples.")


if __name__ == "__main__":
    for diagonal in (0, 1):
        verify(diagonal)
    print("All checks passed.")
