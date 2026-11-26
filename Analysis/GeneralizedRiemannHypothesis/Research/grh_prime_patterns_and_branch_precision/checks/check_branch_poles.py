"""Exact polynomial checks for Lubin--Tate branch interpolation.

The coefficient ring for these examples is Z/p**r.  The same computations
also represent the unramified extension with residue size q=p**f, since the
standard Lubin--Tate polynomials have coefficients in Z.
"""
from collections import Counter
from itertools import combinations, combinations_with_replacement
from math import comb


def multiply(left, right, modulus):
    result = Counter()
    for i, x in left.items():
        for j, y in right.items():
            result[i + j] = (result[i + j] + x * y) % modulus
    return {i: x for i, x in result.items() if x}


def add(left, right, modulus):
    return {i: x for i in left.keys() | right.keys()
            if (x := (left.get(i, 0) + right.get(i, 0)) % modulus)}


def division_polynomials(p, q, modulus, height):
    result = [{1: 1}]
    for _ in range(height):
        old = result[-1]
        power = {0: 1}
        for _ in range(q):
            power = multiply(power, old, modulus)
        result.append(add(power, {j: p * x for j, x in old.items()}, modulus))
    return result


def pole(p, q, exponents, r):
    modulus = p**r
    factors = division_polynomials(p, q, modulus, max(exponents))
    polynomial = {0: 1}
    for h in exponents:
        polynomial = multiply(polynomial, factors[h], modulus)
    omega = max(polynomial)
    reversed_poly = {omega - j: x for j, x in polynomial.items()}
    assert reversed_poly[0] == 1
    # (1-G)^(-1) = 1 + G + ... + G^(r-1); G has p-divisible coefficients.
    g = {j: -x for j, x in reversed_poly.items() if j}
    total = term = {0: 1}
    for _ in range(r - 1):
        term = multiply(term, g, modulus)
        total = add(total, term, modulus)
    assert multiply(total, reversed_poly, modulus) == {0: 1}
    return omega + max(total)


def order(n, q):
    assert n != 0
    height = 0
    while n % q == 0:
        n //= q
        height += 1
    return height


def check_bounds():
    count = 0
    for p, q in [(2, 2), (3, 3), (2, 4), (5, 5)]:
        for size in range(1, 5):
            for exponents in combinations_with_replacement(range(3), size):
                omega = sum(q**h for h in exponents)
                t = max(exponents)
                m = exponents.count(t)
                for r in range(1, 9):
                    answer = pole(p, q, exponents, r)
                    if t == 0:
                        assert answer == omega
                    else:
                        d = q**t - q**(t - 1)
                        upper = omega + (r - 1) * d
                        assert upper - (m - 1) * d <= answer <= upper
                        assert (answer == upper) == (comb(m + r - 2, r - 1) % p != 0)
                    count += 1
    print(f"Validated the slope bounds and saturation in {count} cases.")


def check_designs():
    count = 0
    for p, pool in [(2, range(8)), (3, range(9))]:
        for size in range(2, 6):
            for r in (1, 2, 3, 4):
                values = {}
                def threshold(exponents):
                    key = tuple(sorted(exponents))
                    if key not in values:
                        values[key] = 1 + pole(p, p, key, r)
                    return values[key]
                optimum = threshold([order(i, p) for i in range(1, size)])
                for sample in combinations(pool, size):
                    worst = max(threshold([order(x - y, p) for y in sample if y != x])
                                for x in sample)
                    assert worst >= optimum
                    if sample == tuple(range(size)):
                        assert worst == optimum
                    count += 1
    print(f"Validated the design optimum on {count} finite sampling configurations.")


if __name__ == "__main__":
    check_bounds()
    check_designs()
    print("Q2 with directions 0,4,12; b=0:")
    print("r       ", list(range(1, 11)))
    print("pole    ", [pole(2, 2, [2, 2], r) for r in range(1, 11)])
