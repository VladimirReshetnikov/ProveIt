"""Exact finite test of a quadratic-character quotient for partitions modulo 5."""
from collections import Counter
from fractions import Fraction
from itertools import combinations, product
from math import comb, prod

PRIMES = (11, 19, 29, 31, 41, 59, 61, 71, 13)
QUOTAS = (2, 3, 4)
MODULUS = 5


def parity(p):
    """Encode the signs +1 and -1 of the quadratic character by bits 0 and 1."""
    assert p % 5 != 0
    return int(p % 5 not in (1, 4))


def quotient_dp():
    # The third box is the reference. Its quota and bit follow from the other two.
    k0, k1, k2 = QUOTAS
    states = Counter({(0, 0, 0, 0): 1})
    for seen, p in enumerate(PRIMES):
        bit = parity(p)
        new = Counter()
        for (a, b, u, v), count in states.items():
            if a < k0:
                new[a + 1, b, u ^ bit, v] += count
            if b < k1:
                new[a, b + 1, u, v ^ bit] += count
            if seen - a - b < k2:
                new[a, b, u, v] += count
        states = new
    total_bit = sum(map(parity, PRIMES)) % 2
    return {(u, v, total_bit ^ u ^ v): n for (a, b, u, v), n in states.items()
            if (a, b) == (k0, k1)}


def enumeration():
    counts = Counter()
    k0, k1, _ = QUOTAS
    for first in combinations(PRIMES, k0):
        left = set(PRIMES).difference(first)
        for second in combinations(sorted(left), k1):
            groups = (first, second, left.difference(second))
            target = tuple(prod(group) % MODULUS for group in groups)
            counts[target] += 1
    return counts


def main():
    assert sum(map(parity, PRIMES)) == 1
    total = comb(len(PRIMES), QUOTAS[0]) * comb(len(PRIMES) - QUOTAS[0], QUOTAS[1])
    counts = enumeration()
    cells = quotient_dp()
    assert sum(cells.values()) == sum(counts.values()) == total
    modulus_target = prod(PRIMES) % MODULUS
    fibers = {}
    for t in product(range(1, MODULUS), repeat=3):
        if prod(t) % MODULUS == modulus_target:
            bits = tuple(map(parity, t))
            fibers.setdefault(bits, []).append(t)
    print(f"Total partitions={total}; total product={modulus_target} mod 5")
    for bits, fiber in sorted(fibers.items()):
        n = cells.get(bits, 0)
        values = [counts[t] for t in fiber]
        assert sum(values) == n
        assert (all(values) if n else not any(values))
        label = ''.join('+' if b == 0 else '-' for b in bits)
        print(f"{label}: count={n}, mass={Fraction(n, total)},"
              f" occupied={sum(v > 0 for v in values)}/{len(fiber)},"
              f" fiber counts={sorted(values)}")
    assert set(cells) == {(1, 0, 0), (0, 1, 0), (0, 0, 1)}
    assert len(counts) == 12


if __name__ == "__main__":
    main()
