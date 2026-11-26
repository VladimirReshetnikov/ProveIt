"""Finite part of Erdos 985 and the Grosswald threshold examples. Python 3."""
from math import isqrt


def is_prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def prime_divisors(n):
    divisors = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            divisors.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        divisors.append(n)
    return divisors


def least_generator(p, divisors, candidates):
    for q in candidates:
        if q >= p:
            break
        if all(pow(q, (p-1)//ell, p) != 1 for ell in divisors):
            return q
    raise ValueError(f"No generator among candidates for p={p}")


def main():
    primes = [n for n in range(2, 2792) if is_prime(n)]
    largest = 0
    attaining = []
    for p in primes[1:]:
        divisors = prime_divisors(p-1)
        q = least_generator(p, divisors, primes)
        # Independent exhaustive order check (do not require factorization).
        if len({pow(q, j, p) for j in range(p-1)}) != p-1:
            raise ValueError(f"Invalid witness ({p}, {q})")
        if q >= largest:
            if q > largest:
                largest, attaining = q, []
            attaining.append(p)
        if p in (409, 2791):
            g = least_generator(p, divisors, range(2, p))
            print(f"p={p}: least generator {g}, least prime generator {q}")
    print(f"All {len(primes)-1} odd primes up to 2791 have a prime generator below p.")
    print(f"Largest least prime generator: {largest}, attained at {attaining}.")


if __name__ == "__main__":
    main()
