"""Exact fixed-cardinality prime-product counts. Uses the Python standard library."""
from collections import Counter
from fractions import Fraction
from itertools import combinations
from math import comb, gcd, isqrt, prod


def primes_to(limit):
    return [n for n in range(2, limit + 1)
            if all(n % d for d in range(2, isqrt(n) + 1))]


def subset_counts(primes, modulus, size):
    layers = [Counter({1: 1})] + [Counter() for _ in range(size)]
    for i, prime in enumerate(primes):
        for j in range(min(i, size - 1), -1, -1):
            for value, count in layers[j].items():
                layers[j + 1][(value * prime) % modulus] += count
    result = layers[size]
    assert sum(result.values()) == comb(len(primes), size)
    return result


def summarize(label, primes, q, k):
    counts = subset_counts(primes, q, k)
    units = [a for a in range(1, q) if gcd(a, q) == 1]
    total = sum(counts.values())
    relative_error = max(abs(Fraction(len(units) * counts[a], total) - 1)
                         for a in units)
    print(f'{label}: M={len(primes)}, k={k}, total={total}, '
          f'classes={len(counts)}, min={min(counts[a] for a in units)}, '
          f'max={max(counts.values())}, max_relative_error={relative_error}')
    return counts


def main():
    q, x, k = 101, 251, 14
    pool = [p for p in primes_to(x) if p % q]
    residues = [p for p in pool if pow(p, (q - 1) // 2, q) == 1]
    others = [p for p in pool if p not in residues]
    print(f'q={q}, x={x}, N={len(pool)}, quadratic residues={len(residues)}')
    retained = residues + others[:9]
    result = summarize('all quadratic residues plus nine nonresidue primes',
                       retained, q, k)
    assert len(result) == q - 1
    blocked = summarize('only quadratic residues', residues, q, k)
    assert all(pow(a, (q - 1) // 2, q) == 1 for a in blocked)
    subset = pool[:13]
    for j in range(len(subset) + 1):
        direct = Counter(prod(c) % q for c in combinations(subset, j))
        assert subset_counts(subset, q, j) == direct
    # Complementation pairs products by a -> product(A)/a.
    comp = subset_counts(retained, q, len(retained) - k)
    full_product = prod(retained) % q
    assert all(comp[full_product * pow(a, -1, q) % q] == v
               for a, v in result.items())
    print('Direct enumeration for all 14 subset sizes and complement identity passed.')


if __name__ == '__main__':
    main()
