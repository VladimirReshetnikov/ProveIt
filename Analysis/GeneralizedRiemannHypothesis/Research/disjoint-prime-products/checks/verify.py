"""Exact checks for disjoint prime products and their quadratic and cubic projections.

Run with Python 3.8 or later. The residue dynamic program is for two
reported blocks. The urn enumeration accepts any number of blocks.
"""

from collections import Counter
from fractions import Fraction
from itertools import combinations, product
from math import comb, exp, gcd, isqrt, prod


def primes_to(cutoff):
    return [
        n for n in range(2, cutoff + 1)
        if all(n % d != 0 for d in range(2, isqrt(n) + 1))
    ]


def sign_bit(x, q):
    """Return 1 for a quadratic nonresidue, 0 for a quadratic residue."""
    assert gcd(x, q) == 1
    return int(pow(x, (q - 1) // 2, q) == q - 1)


def residue_dp(pool, q, first, second):
    # The three choices for each input prime are unused, first, or second.
    counts = Counter({(0, 0, 1, 1): 1})
    for p in pool:
        next_counts = counts.copy()
        for (i, j, a, b), count in counts.items():
            if i < first:
                next_counts[i + 1, j, (a * p) % q, b] += count
            if j < second:
                next_counts[i, j + 1, a, (b * p) % q] += count
        counts = next_counts
    return Counter({
        (a, b): count for (i, j, a, b), count in counts.items()
        if i == first and j == second
    })


def residue_brute_force(pool, q, first, second):
    counts = Counter()
    for block in combinations(pool, first):
        other = [p for p in pool if p not in block]
        a = prod(block) % q
        for block2 in combinations(other, second):
            counts[a, prod(block2) % q] += 1
    return counts


def urn_counts(sizes, minority):
    """Place minority positions among fixed cells. Cell 0 is unreported."""
    counts = Counter()
    for occupancy in product(*(range(min(n, minority) + 1) for n in sizes)):
        if sum(occupancy) == minority:
            signs = tuple(x % 2 for x in occupancy[1:])
            counts[signs] += prod(comb(n, x) for n, x in zip(sizes, occupancy))
    return counts


def parity_numerator(m, k, s):
    return sum(
        (-1)**j * comb(k, j) * comb(m - k, s - j)
        for j in range(max(0, s - m + k), min(k, s) + 1)
    )


def support_from_capacities(sizes, minority, signs):
    all_signs = ((minority - sum(signs)) % 2,) + signs
    lower = sum(all_signs)
    capacity = sum(n - (n - bit) % 2 for n, bit in zip(sizes, all_signs))
    return lower <= minority <= capacity


def exhaust_urns():
    cases = 0
    transforms = 0
    for r, max_size in ((1, 8), (2, 5), (3, 4)):
        all_masks = tuple(product((0, 1), repeat=r))
        for sizes in product(range(1, max_size + 1), repeat=r + 1):
            m = sum(sizes)
            for s in range(m // 2 + 1):
                counts = urn_counts(sizes, s)
                assert sum(counts.values()) == comb(m, s)
                for mask in all_masks:
                    assert (counts[mask] > 0) == support_from_capacities(sizes, s, mask)
                    if m - s >= r + 1:
                        weight = sum(mask) + (s - sum(mask)) % 2
                        assert (counts[mask] > 0) == (weight <= s)
                    k = sum(n * v for n, v in zip(sizes[1:], mask))
                    transform = sum(
                        (-1)**sum(a*b for a, b in zip(state, mask)) * count
                        for state, count in counts.items()
                    )
                    assert transform == parity_numerator(m, k, s)
                    transforms += 1
                if m - s >= r + 1:
                    assert (len(counts) == len(all_masks)) == (s >= r)
                cases += 1
    print(f"Exact urn checks: {cases} cases, {transforms} Fourier coefficients.")


def prime_examples():
    q = 11
    eligible = [p for p in primes_to(199) if p != q]
    plus = [p for p in eligible if not sign_bit(p, q)]
    minus = [p for p in eligible if sign_bit(p, q)]
    print("Prime example: q=11, p<=199, m=18, block sizes (6,6,6).")
    print("Retain the first 18-s residue primes and first s nonresidue primes.")
    sizes = (6, 6, 6)
    m = sum(sizes)
    partitions = comb(m, 6) * comb(m - 6, 6)
    for s in range(3):
        pool = sorted(plus[:m-s] + minus[:s])
        observed = residue_dp(pool, q, 6, 6)
        assert sum(observed.values()) == partitions
        urn = urn_counts(sizes, s)
        observed_signs = Counter()
        expected_pairs = set()
        for (a, b), count in observed.items():
            observed_signs[sign_bit(a, q), sign_bit(b, q)] += count
        for a, b in product(range(1, q), repeat=2):
            signs = (sign_bit(a, q), sign_bit(b, q))
            if urn[signs] > 0:
                expected_pairs.add((a, b))
        assert set(observed) == expected_pairs
        print(f"  s={s}: {len(observed)}/100 residue pairs reached")
        for signs in product((0, 1), repeat=2):
            sign_text = "".join("-" if v else "+" for v in signs)
            cells = [
                observed[a, b] for a, b in product(range(1, q), repeat=2)
                if (sign_bit(a, q), sign_bit(b, q)) == signs
            ]
            assert Fraction(observed_signs[signs], partitions) == Fraction(urn[signs], comb(m, s))
            print(f"    {sign_text}: {sum(cells):>9} assignments, per-pair counts {min(cells)}..{max(cells)}")
    small = [2, 3, 5, 11, 13, 17, 19, 23]
    small_dp = residue_dp(small, 7, 2, 3)
    assert small_dp == residue_brute_force(small, 7, 2, 3)
    print(f"Independent direct enumeration: all {sum(small_dp.values())} assignments agree (q=7).")


def cubic_profiles(sizes):
    """All allocations of 0,+1,-1 entries, compressed by their cell residues."""
    states = {(0, 0, ())}
    for cell, size in enumerate(sizes):
        after = set()
        for u, v, residues in states:
            for plus in range(size + 1):
                for minus in range(size - plus + 1):
                    residue = (plus - minus) % 3
                    target = residues + (residue,) if cell else residues
                    after.add((u + plus, v + minus, target))
        states = after
    return states


def cubic_feasible(u, v, target):
    i, j = target.count(1), target.count(2)
    return 2*u + v >= 2*i + j and u + 2*v >= i + 2*j


def exhaust_cubic_urns():
    profiles, tests = 0, 0
    for r in (1, 2, 3):
        targets = tuple(product(range(3), repeat=r))
        for sizes in product((2*r, 2*r + 1), repeat=r + 1):
            m = sum(sizes)
            states = cubic_profiles(sizes)
            for u in range(m - 2*r + 1):
                for v in range(m - 2*r - u + 1):
                    observed = [target for target in targets if (u, v, target) in states]
                    expected = [target for target in targets if cubic_feasible(u, v, target)]
                    assert observed == expected
                    assert (len(observed) == len(targets)) == (u+v+min(u, v) >= 2*r)
                    profiles += 1
                    tests += len(targets)
    print(f"Exact cubic checks: {profiles} capacity and inventory profiles, {tests} target vectors.")


def cubic_prime_example():
    q, cutoff, m = 13, 239, 15
    exponent = {1: 0, 3: 1, 9: 2}  # The order-three subgroup of the units modulo 13.
    def character(p):
        return exponent[pow(p, 4, q)]
    eligible = [p for p in primes_to(cutoff) if p != q]
    classes = [[p for p in eligible if character(p) == value] for value in range(3)]
    print("Cubic example: q=13, p<=239, m=15, block sizes (5,5,5).")
    print("Take the smallest requested number of primes in each character class.")
    for u, v in ((0, 0), (1, 1), (2, 0), (2, 1)):
        pool = sorted(classes[0][:m-u-v] + classes[1][:u] + classes[2][:v])
        assert len(pool) == m
        observed = residue_dp(pool, q, 5, 5)
        assert sum(observed.values()) == comb(m, 5) * comb(m-5, 5)
        expected = {
            (a, b) for a, b in product(range(1, q), repeat=2)
            if cubic_feasible(u, v, (character(a), character(b)))
        }
        assert set(observed) == expected
        print(f"  u={u}, v={v}: {len(observed)}/144 residue pairs, "
              f"{len(observed)//16}/9 cubic fibres.")


def sparse_example():
    print("Sparse regime: m=t^2, s=t, smallest block size k=t.")
    print("  t       exact parity     binomial parity    Poisson limit")
    for t in (10, 30, 100, 300):
        m = t*t
        exact = Fraction(parity_numerator(m, t, t), comb(m, t))
        independent = Fraction(m-2*t, m)**t
        print(f"{t:4d}     {float(exact):.9f}       {float(independent):.9f}      {exp(-2):.9f}")


if __name__ == "__main__":
    exhaust_urns()
    prime_examples()
    exhaust_cubic_urns()
    cubic_prime_example()
    sparse_example()
