"""Finite prime-side illustration of the compactly supported sinc probe.

Run with Python 3 and the standard library. All reported kernel sums use
floating point. They illustrate the argument and are not used as proof.
"""
import math
from bisect import bisect_left, bisect_right


def prime_powers(limit):
    sieve = bytearray([1]) * (limit + 1)
    sieve[:2] = bytes(2)
    for p in range(2, math.isqrt(limit) + 1):
        if sieve[p]:
            count = (limit - p * p) // p + 1
            sieve[p * p :: p] = bytes(count)
    powers = []
    for p in range(2, limit + 1):
        if sieve[p]:
            n = p
            while n <= limit:
                powers.append((n, p))
                n *= p
    return sorted(powers)


def quartic_character(q, generator):
    roots = (1, 1j, -1, -1j)
    values = [0] * q
    x = 1
    for exponent in range(q - 1):
        assert values[x] == 0, "generator has insufficient order"
        values[x] = roots[exponent % 4]
        x = (x * generator) % q
    assert x == 1 and all(values[1:])
    return values


def kernel(v, width, bandwidth):
    ratio = v / width
    if abs(ratio) >= 1:
        return 0.
    envelope = math.exp(-(ratio * ratio) / (1 - ratio * ratio))
    z = bandwidth * v
    sinc = math.sin(z) / z if z else 1.
    return envelope * sinc * sinc


def main():
    x = 4096
    width = .1
    bandwidth = 16 * x / math.log(x)
    q = 101
    character = quartic_character(q, 2)
    powers = prime_powers(math.ceil(2 * x * math.exp(width)))
    numbers = [n for n, _ in powers]
    primes = [n for n, p in powers if p == n and x < p <= 2 * x]
    records = []
    for p in primes:
        if not character[p % q].imag:
            continue
        lower = bisect_left(numbers, p * math.exp(-width))
        upper = bisect_right(numbers, p * math.exp(width))
        filtered = 0j
        leakage = 0.
        for n, base in powers[lower:upper]:
            weight = (math.sqrt(p / n) * math.log(base) / math.log(p)
                      * kernel(math.log(n / p), width, bandwidth))
            difference = 2j * character[n % q].imag
            filtered += weight * difference
            if n != p:
                leakage += weight
        records.append((leakage, p, filtered))
    records.sort()
    print(f"Conjugate primitive quartic characters modulo {q}, chi(2) = i.")
    print(f"X = {x}, B = 16X/log X = {bandwidth:.6f}, support radius = {width}.")
    print(f"Primes in (X,2X]: {len(primes)}")
    print(f"Primes with |chi(p) - conjugate(chi(p))| = 2: {len(records)}")
    for threshold in (.01, .1, .25):
        print(f"Distinguishing primes with leakage <= {threshold}: "
              f"{sum(leakage <= threshold for leakage, _, _ in records)}")
    leakage, p, filtered = records[len(records) // 2]
    raw = 2j * character[p % q].imag
    print(f"Median-leakage distinguishing prime: {p}")
    print(f"Normalized main term: {raw.imag:+.8f}i")
    print(f"Normalized full arithmetic probe: {filtered.imag:+.8f}i")
    print(f"Positive sum of all off-diagonal weights: {leakage:.8f}")
    assert abs(filtered - raw) <= 2 * leakage + 1e-9


if __name__ == "__main__":
    main()
