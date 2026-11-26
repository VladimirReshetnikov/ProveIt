"""Certify the finite cases for a prime plus a multiple of a prime cube."""
from math import isqrt


def sieve(bound):
    flags = bytearray([1]) * (bound + 1)
    flags[:2] = bytes(2)
    for i in range(2, isqrt(bound) + 1):
        if flags[i]:
            flags[i*i::i] = bytes((bound - i*i)//i + 1)
    return flags


def max_least_prime(q, primes):
    modulus = q**3
    target = (q - 1) * q*q
    residues = set()
    for p in primes:
        if p != q:
            residues.add(p % modulus)
        if len(residues) == target:
            return p
    raise ValueError(f"Incomplete coverage for q={q}")


def representable(n, primes, flags):
    for r in primes:
        cube = r**3
        if cube >= n:
            return False
        if any(flags[n-w] for w in range(cube, n, cube)):
            return True
    raise ValueError("Insufficient prime table")


flags = sieve(8_000_000)
primes = [i for i, b in enumerate(flags) if b]
primorial = 1
exceptions = []
print("q  max_least_prime  candidates  exceptions")
for q in primes:
    if q >= 43:
        if primorial <= q**8:
            raise ValueError(f"Failed primorial check for q={q}")
        if q == 257:
            break
    else:
        maximum = max_least_prime(q, primes)
        candidates = [n for n in range(primorial, maximum+1, primorial) if n % q]
        bad = [n for n in candidates if not representable(n, primes, flags)]
        print(q, maximum, len(candidates), len(bad))
        exceptions.extend(bad)
    primorial *= q

exceptions.sort()
print("Count:", len(exceptions))
print("Exceptions:", *exceptions)
if (len(exceptions), max(exceptions)) != (62, 10500):
    raise ValueError("Conclusion differs from the stated theorem")
