"""Verify the two-spoke construction with exact integer arithmetic."""
from fractions import Fraction
from itertools import combinations, product
from functools import lru_cache
from math import isqrt, prod

from rankin import primes_through


DIGITS = (0, 1, 3, 4)


@lru_cache(maxsize=1)
def chosen_primes():
    return tuple(primes_through(1699))


def positive_pair(p, r):
    """p < r are two odd primes from the chosen list."""
    return 4*p*p*r*r > 27*((p+1)*(r+1) + p**4)


def ternary_greedy(v):
    while v > 0:
        v, digit = divmod(v, 3)
        if digit == 2:
            return False
    return True


def in_example(factorization):
    """Membership in E for a positive integer given its prime factorization.

    Input is a mapping from prime bases to nonnegative integer exponents.
    Missing primes have exponent zero. Prime bases are assumed correct.
    """
    primes = chosen_primes()
    selected = set(primes)
    for p, exponent in factorization.items():
        if not isinstance(exponent, int) or exponent < 0:
            raise ValueError("Exponents must be nonnegative integers")
        if p not in selected and not ternary_greedy(exponent):
            return False
    parts = [divmod(factorization.get(p, 0), 9) for p in primes]
    if any(not ternary_greedy(high) for high, low in parts):
        return False
    pivot = parts[0][1]
    active = [(p, low) for p, (_, low) in zip(primes[1:], parts[1:]) if low != 1]
    if pivot == 2:
        return (len(active) <= 2 and all(low == 2 for _, low in active) and
                (len(active) != 2 or positive_pair(active[0][0], active[1][0])))
    if pivot not in DIGITS or any(low not in DIGITS for _, low in active):
        return False
    if len(active) > 2:
        return True
    if len(active) == 2 and not positive_pair(active[0][0], active[1][0]):
        return True
    return not deleted((pivot, *(low for _, low in active)))


def deleted(point):
    pivot, *spokes = point
    active = [digit for digit in spokes if digit != 1]
    if not active:
        return pivot in (1, 3, 4)
    if len(active) == 1:
        return active[0] == 4 or (active[0] == 3 and pivot != 0)
    return tuple(active) == (0, 4) or all(digit in (3, 4) for digit in active)


def check_covers():
    for k, expected in enumerate((4, 12, 40)):
        edges = set()
        for end in product(DIGITS, repeat=k + 1):
            # New middle x=(2,...,2), or new endpoint x and old middle end.
            for other in (tuple(4 - j for j in end), tuple(2 * j - 2 for j in end)):
                if all(j in DIGITS for j in other):
                    edges.add(tuple(sorted((end, other))))
        assert len(edges) == expected
        assert all(deleted(a) or deleted(b) for a, b in edges)
        print("Support size", k, "covered edges", len(edges))


def main():
    check_covers()
    base = dict.fromkeys(chosen_primes(), 1)
    assert not in_example(base)                    # P
    assert in_example({**base, 2: 2})             # 2P
    assert in_example({**base, 2: 2, 3: 2})       # 2*3*P
    assert in_example({}) and not in_example({1709: 2})
    # The true gain is at least this integer rounded down / scale.
    scale = 10**15
    primes = [p for p in range(3, 1700, 2) if all(p % d for d in range(2, isqrt(p) + 1))]
    lower = -7 * scale // 8
    normalized = Fraction(-7, 8)
    for p in primes:
        normalized += Fraction(4 * p*p - 11*p - 27, 8*p**3)
        lower += (scale * (4 * p * p - 11 * p - 27)) // (8 * p**3)
    count = 0
    assert (2, *primes) == chosen_primes()
    for p, r in combinations(primes, 2):
        # 8 p^3 r^3 times the pair gain.
        numerator = 4 * p**2 * r**2 - 27 * ((p + 1) * (r + 1) + p**4)
        assert (numerator > 0) == positive_pair(p, r)
        if numerator > 0:
            normalized += Fraction(numerator, 8 * p**3 * r**3)
            count += 1
            lower += (scale * numerator) // (8 * p**3 * r**3)
    assert lower > 73 * scale // 1000000
    prime_product = 2 * prod(primes)
    totient = prod(p - 1 for p in primes)  # The omitted factor from p=2 is one.
    print("Ordinary primes through 1699:", len(primes) + 1, "chosen pairs:", count)
    print("Normalized margin at least", Fraction(lower, scale))
    # Outside greedy product >= 1/zeta(2) > 1/2. High-digit factors >= 1.
    # Finite normalizing factor is totient/prime_product**2.
    assert lower * totient * 10**728 > 2 * scale * prime_product**2
    print("Absolute density improvement exceeds 10^-728")


    # Since A=C+9A, all higher digit factors cancel in d(E)/d(G).
    relative = normalized * prod(Fraction(p**3, (p+1)*(p**3+1)) for p in [2] + primes)
    scaled = relative * 10**727
    assert Fraction(2185320021572, 10**12) < scaled < Fraction(2185320021573, 10**12)
    print('10^727 times relative gain in (2.185320021572, 2.185320021573)')

    # For p <= T, keep ternary positions 1,3,9 in the old exponent.
    # Any omitted admissible exponent is >=27. Beyond T, only prime
    # squares can cause rejection. Both bounds use the union bound.
    cutoff, accuracy = 100_000, 10**18
    lo = hi = accuracy
    for p in primes_through(cutoff):
        den = p**14
        num = (p-1)*(p+1)*(p**3+1)*(p**9+1)
        lo = lo*num // den
        hi = -(-hi*num // den)
    small_tail = Fraction(1, 2**27) + Fraction(1, 26 * 2**26)
    rankin_lo = Fraction(lo, accuracy) - Fraction(1, cutoff)
    rankin_hi = Fraction(hi, accuracy) + small_tail
    assert Fraction(15728, 10000) < scaled * rankin_lo
    assert scaled * rankin_hi < Fraction(15730, 10000)
    print('1.5728 < 10^727 times absolute density gain < 1.5730')


if __name__ == "__main__":
    main()
