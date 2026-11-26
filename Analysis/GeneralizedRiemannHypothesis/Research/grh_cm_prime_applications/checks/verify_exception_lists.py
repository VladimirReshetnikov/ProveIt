"""Independent all-integers check of both additive lists up to two million."""
from math import isqrt
from pathlib import Path

LIMIT = 2_000_000
HERE = Path(__file__).parent


def prime_table(n):
    flags = bytearray([1]) * (n + 1)
    flags[:2] = bytes(2)
    for p in range(2, isqrt(n) + 1):
        if flags[p]:
            count = 1 + (n - p*p) // p
            flags[p*p::p] = bytes(count)
    return flags


def all_exceptions(k, flags):
    packed = bytearray(LIMIT // 8 + 1)
    for p, prime in enumerate(flags):
        if prime:
            packed[p // 8] |= 1 << (p % 8)
    primes = int.from_bytes(packed, "little")
    valid_bits = (1 << (LIMIT + 1)) - 1
    represented = 0
    for r, prime in enumerate(flags):
        step = r ** k
        if step > LIMIT:
            break
        if not prime:
            continue
        # Start with multiplier one. Each shift doubles the consecutive range
        # of positive multipliers, independently of every other prime base.
        current = (primes << step) & valid_bits
        shift = step
        while shift <= LIMIT:
            current |= (current << shift) & valid_bits
            shift *= 2
        represented |= current
    missing = (valid_bits & ~1) ^ represented
    bad = []
    while missing:
        lowest_bit = missing & -missing
        bad.append(lowest_bit.bit_length() - 1)
        missing ^= lowest_bit
    return bad


if __name__ == "__main__":
    flags = prime_table(LIMIT)
    for k, name in [(3, "cube.out"), (4, "fourth.out")]:
        reference = (HERE / name).read_text().split("Exceptions:")[-1]
        expected = [int(word) for word in reference.split()]
        actual = all_exceptions(k, flags)
        if actual != expected:
            raise ValueError(f"The lists differ for exponent {k}")
        print(f"Power {k}: all {len(actual)} exceptions through {LIMIT:,} match.")
