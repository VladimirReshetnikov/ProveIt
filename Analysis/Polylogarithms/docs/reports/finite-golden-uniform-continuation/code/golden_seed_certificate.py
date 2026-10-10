#!/usr/bin/env python3
"""Exact finite certificates for the golden multiplicative-seed theorem.

Only Python's standard library is required.  The infinite cutoff uses
Flatters, arXiv:0708.2190, Theorem 1.4; this script does not purport to
reprove that theorem.  All algebraic identities, primalities, residue-field
orders, and the finite relation ranks below are checked exactly.
"""
from __future__ import annotations

from fractions import Fraction as Q
import json


def prime_factors(n: int) -> list[int]:
    n = abs(n)
    result = []
    p = 2
    while p * p <= n:
        if n % p == 0:
            result.append(p)
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        result.append(n)
    return result


def is_prime(n: int) -> bool:
    return n >= 2 and prime_factors(n) == [n]


# a + b*r, with r^2+r-1=0.
def mul(x, y):
    a, b = x
    c, d = y
    return (a * c + b * d, a * d + b * c - b * d)


def inv(x):
    a, b = x
    norm = a * a - a * b - b * b
    assert norm != 0
    return (Q(a - b, norm), Q(-b, norm))


def power(x, n: int):
    if n < 0:
        return power(inv(x), -n)
    y = (Q(1), Q(0))
    while n:
        if n & 1:
            y = mul(y, x)
        x = mul(x, x)
        n //= 2
    return y


R = (Q(0), Q(1))
ONE = (Q(1), Q(0))


def v(n: int):
    a, b = power(R, n)
    return (1 - a, -b)


def norm(x):
    a, b = x
    return a * a - a * b - b * b


RELATIONS = [
    ({1: 1}, 2),
    ({2: 1}, 1),
    ({6: 1, 3: -2}, -1),
    ({12: 1, 4: -1, 3: -3}, -2),
    ({20: 1, 4: -3, 10: -1}, -1),
    ({24: 1, 4: 1, 3: -4, 8: -2}, -2),
]
EXCEPTIONS = {1, 2, 6, 12, 20, 24}


def modpow_pair(x, n: int, p: int):
    y = (1, 0)
    while n:
        if n & 1:
            y = tuple(z % p for z in mul(y, x))
        x = tuple(z % p for z in mul(x, x))
        n //= 2
    return y


def primitive_witness(n: int):
    """A prime ideal with r of exact order n in its residue field."""
    for p in prime_factors(int(norm(v(n)))):
        assert is_prime(p)
        roots = [a for a in range(p) if (a * a + a - 1) % p == 0]
        if roots:
            for a in roots:
                if pow(a, n, p) != 1:
                    continue
                residues = {str(ell): pow(a, n // ell, p)
                            for ell in prime_factors(n)}
                if all(z != 1 for z in residues.values()):
                    return {"n": n, "prime": p,
                            "ideal": f"({p}, r-{a})",
                            "residue_degree": 1,
                            "r_residue": a,
                            "proper_power_checks": residues}
        else:
            # Degree-two polynomial without a root over F_p is irreducible.
            if modpow_pair((0, 1), n, p) != (1, 0):
                continue
            residues = {str(ell): modpow_pair((0, 1), n // ell, p)
                        for ell in prime_factors(n)}
            if all(z != (1, 0) for z in residues.values()):
                return {"n": n, "prime": p, "ideal": f"({p})",
                        "residue_degree": 2, "r_residue": "theta",
                        "proper_power_checks": residues}
    return None


def rank(rows):
    if not rows:
        return 0
    a = [[Q(x) for x in row] for row in rows]
    pivot_row = 0
    for col in range(len(a[0])):
        candidate = next((i for i in range(pivot_row, len(a))
                          if a[i][col]), None)
        if candidate is None:
            continue
        a[pivot_row], a[candidate] = a[candidate], a[pivot_row]
        pivot = a[pivot_row][col]
        a[pivot_row] = [x / pivot for x in a[pivot_row]]
        for i in range(len(a)):
            if i != pivot_row and a[i][col]:
                factor = a[i][col]
                a[i] = [x - factor * y
                        for x, y in zip(a[i], a[pivot_row])]
        pivot_row += 1
        if pivot_row == len(a):
            break
    return pivot_row


def main():
    exact_rows = []
    for c, b in RELATIONS:
        value = ONE
        for n, exponent in c.items():
            value = mul(value, power(v(n), exponent))
        assert value == power(R, b), (c, b, value)
        exact_rows.append({"coefficients": c, "rho_exponent": b,
                           "verified": True})

    witnesses = []
    for n in range(1, 25):
        witness = primitive_witness(n)
        if n in EXCEPTIONS:
            assert witness is None
        else:
            assert witness is not None, n
            witnesses.append(witness)

    restrictions = {}
    for h in range(1, 26):
        constraints = [[row.get(n, 0) for row, _ in RELATIONS]
                       for n in range(1, 25) if n % h]
        dimension = len(RELATIONS) - rank(constraints)
        expected = {1: 6, 2: 4, 3: 1, 4: 1}.get(h, 0)
        assert dimension == expected, (h, dimension)
        restrictions[str(h)] = dimension

    # Independently verify the primitive integer relations for h=3 and h=4.
    for h, c, base_exponent in [
        (3, {2: 3, 1: -6}, -1),
        (4, {3: 8, 2: 12, 1: -14, 6: -6}, -1),
    ]:
        value = ONE
        for k, exponent in c.items():
            value = mul(value, power(v(h * k), exponent))
        assert value == power(R, h * base_exponent)

    report = {
        "arithmetic": "exact integer and rational arithmetic only",
        "cutoff_input": "Flatters, arXiv:0708.2190, Theorem 1.4",
        "relations": exact_rows,
        "primitive_prime_ideal_witnesses": witnesses,
        "restricted_rational_seed_ranks": restrictions,
        "checked_identity_count": len(RELATIONS) + 2,
        "checked_primitive_witness_count": len(witnesses),
    }
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
