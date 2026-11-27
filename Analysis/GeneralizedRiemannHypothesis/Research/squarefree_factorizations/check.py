"""Exact finite examples for fixed-size partitions of primes, using Python 3."""
from collections import Counter
from itertools import combinations, product
from math import comb, gcd, prod, tau
from cmath import exp

# The prime-power unit groups below are cyclic; each tuple lists their factors.
FACTORS = {6: (3,), 9: (9,), 12: (3, 4), 15: (3, 5), 20: (4, 5)}
GENERATOR = {3: 2, 4: 3, 5: 2, 9: 2}
POOL = (3, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149,
        151, 157, 163, 167, 173)
DELETED = {97}


def units(q):
    return [a for a in range(q) if gcd(a, q) == 1]


def characters(q):
    """All characters on the units, from CRT and cyclic-group logarithms."""
    logs = []
    for factor in FACTORS[q]:
        base = GENERATOR[factor]
        size = len(units(factor))
        table = {pow(base, j, factor): j for j in range(size)}
        assert len(table) == size
        logs.append((factor, size, table))
    for frequencies in product(*(range(size) for _, size, _ in logs)):
        yield {a: exp(1j * tau * sum(h * table[a % f] / size
                                    for h, (f, size, table)
                                    in zip(frequencies, logs)))
               for a in units(q)}


def partition_counts(points, moduli, k):
    """Enumerate each ordered three-way partition with box sizes (k,k,k)."""
    q0, q1, q2 = moduli
    counts = Counter()
    all_points = set(points)
    for first in combinations(points, k):
        a = prod(first) % q0
        remaining = all_points.difference(first)
        total = prod(remaining)
        for second in combinations(sorted(remaining), k):
            second_product = prod(second)
            counts[a, second_product % q1, (total // second_product) % q2] += 1
    return counts


def coefficient(points, moduli, chars, k):
    """Coefficient of z0^k z1^k z2^k by independent polynomial multiplication."""
    terms = {(0, 0): 1.0 + 0j}
    for i, p in enumerate(points):
        values = [chi[p % q] for chi, q in zip(chars, moduli)]
        new = {}
        for (a, b), c in terms.items():
            for j, (u, v) in enumerate(((a + 1, b), (a, b + 1), (a, b))):
                if max(u, v, i + 1 - u - v) <= k:
                    new[u, v] = new.get((u, v), 0j) + c * values[j]
        terms = new
    return terms[k, k]


def run_example(moduli):
    points = tuple(p for p in POOL if p not in DELETED and gcd(p, prod(moduli)) == 1)
    k, rem = divmod(len(points), 3)
    assert not rem and k == 5
    counts = partition_counts(points, moduli, k)
    total = comb(3 * k, k) * comb(2 * k, k)
    assert sum(counts.values()) == total
    g = gcd(*moduli)
    omega = set(product(*(units(q) for q in moduli)))
    allowed = {v for v in omega if (prod(v) - prod(points)) % g == 0}
    assert set(counts) == allowed
    assert len(allowed) * len(units(g)) == len(omega)

    checks = 0
    for chars in product(*(characters(q) for q in moduli)):
        fourier = sum(n * prod(chi[a] for a, chi in zip(v, chars))
                      for v, n in counts.items())
        coeff = coefficient(points, moduli, chars, k)
        assert abs(fourier - coeff) < 1e-10 * total
        checks += 1
    lo, hi = min(counts.values()), max(counts.values())
    relative = max(abs(lo * len(allowed) - total), abs(hi * len(allowed) - total)) / total
    print(f"q={moduli}, common gcd={g}, surviving primes={len(points)}, quotas=({k},{k},{k})")
    print(f"  support={len(allowed)}/{len(omega)}, partitions={total},"
          f" counts=[{lo},{hi}], max relative error={relative:.6f}")
    print(f"  checked {checks} Fourier coefficients")


def erasure_example():
    # Six distinct primes, equally split between the two residue classes.
    points = (7, 13, 19, 5, 11, 17)
    survivors = tuple(p for p in points if p % 3 == 2)
    residues = {prod(pair) % 3 for pair in combinations(survivors, 2)}
    assert len(survivors) == 3 and residues == {1}
    print("q=3: deleting 3 of 6 leaves three primes equal to 2 mod 3;"
          " every 2-subset has product 1 mod 3.")


if __name__ == "__main__":
    run_example((12, 15, 20))
    run_example((6, 9, 12))
    erasure_example()
