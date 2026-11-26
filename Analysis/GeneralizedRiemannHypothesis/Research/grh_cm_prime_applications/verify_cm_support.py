"""Check reduced-form witnesses for sparse-equation bounds using integer arithmetic."""

from math import gcd, isqrt


def reduced_forms(discriminant):
    """Enumerate one primitive reduced form per proper class."""
    if discriminant >= 0 or discriminant % 4 not in (0, 1):
        raise ValueError("expected a negative quadratic order discriminant")
    for a in range(1, isqrt((-discriminant) // 3) + 1):
        for b in range(-a, a + 1):
            c, remainder = divmod(b * b - discriminant, 4 * a)
            if remainder or c < a or gcd(gcd(a, b), c) != 1:
                continue
            if b < 0 and (b == -a or a == c):
                continue
            yield (a, b, c)


def witnesses(discriminant):
    value = -discriminant
    is_even = value % 4 == 0
    n = value // 4 if is_even else value
    for u in range(1, isqrt(n) + 1):
        v, remainder = divmod(n, u)
        if remainder or gcd(u, v) != 1:
            continue
        if is_even:
            yield (u, 0, v)
        elif v > 3 * u:
            yield (u, u, (u + v) // 4)
        else:
            a = (u + v) // 4
            yield (a, (v - u) // 2, a)


def split_denominator_count(discriminant):
    """Count denominators built from split odd primes and a square 2-part."""
    bound = isqrt(isqrt(-discriminant))
    # Every 2-part of 4a (a <= bound) divides this power of two.
    assert (discriminant - 1) % (1 << (bound.bit_length() + 1)) == 0
    primes = bytearray([1]) * (bound + 1)
    admissible = bytearray([1]) * (bound + 1)
    for prime in range(2, bound + 1):
        if not primes[prime]:
            continue
        for multiple in range(prime * prime, bound + 1, prime):
            primes[multiple] = 0
        if prime != 2 and pow(discriminant, (prime - 1) // 2, prime) != 1:
            for multiple in range(prime, bound + 1, prime):
                admissible[multiple] = 0
    return bound, sum(admissible[1:])


def main():
    for size in range(5, 5001):
        if (-size) % 4 not in (0, 1):
            continue
        pairs = list(witnesses(-size))
        assert len(pairs) == len(set(pairs))
        assert set(pairs) <= set(reduced_forms(-size))
    print("All witness lists through absolute discriminant 5000 verified.")
    for n, expected_u in [(30, (1, 2, 3, 5)), (210, (1, 2, 3, 5, 6, 7, 10, 14))]:
        forms = list(reduced_forms(-4 * n))
        assert forms == [(u, 0, n // u) for u in expected_u]
        print(f"Delta = {-4*n}: h = {len(forms)}, minimum support = {len(forms)+1}")

    discriminant = 1 - 2**61
    bound, count = split_denominator_count(discriminant)
    assert (bound, count) == (38967, 7958)
    print(f"Delta = {discriminant}: {count} witnesses up to {bound}, support >= {count+1}.")


if __name__ == "__main__":
    main()
