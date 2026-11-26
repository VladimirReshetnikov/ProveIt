"""Certify the exceptions for a prime plus a positive multiple of a fourth power."""
from array import array
from math import isqrt


def sieve(bound):
    flags = bytearray([1]) * (bound + 1)
    flags[:2] = bytes(2)
    for p in range(2, isqrt(bound) + 1):
        if flags[p]:
            flags[p*p::p] = bytes((bound - p*p)//p + 1)
    return flags


def max_least_prime(q):
    modulus = q**4
    seen = bytearray(modulus)
    missing = q**3 * (q-1)
    for p in primes:
        r = p % modulus
        if p != q and not seen[r]:
            seen[r] = 1
            missing -= 1
            if not missing:
                return p
    raise ValueError(f"Incomplete coverage for q={q}")


def representable(n):
    for r in primes:
        power = r**4
        if power >= n:
            return False
        if n % r == 0:
            if (n-r) % power == 0:
                return True
        elif any(flags[n-w] for w in range(power, n, power)):
            return True
    raise ValueError("Insufficient prime table")


def is_prime(n):
    if n < len(flags):
        return bool(flags[n])
    if isqrt(n) >= len(flags):
        raise ValueError("Insufficient trial divisors")
    for p in primes:
        if p*p > n:
            return True
        if n % p == 0:
            return False
    raise ValueError("Insufficient prime table")


flags = sieve(50_000_000)
primes = array('I', (p for p, b in enumerate(flags) if b))
primorial = 1
exceptions = []
print("q  small_candidates  exceptions  maximum_or_witness_bound")
for q in primes:
    if q >= 53:
        if primorial <= q**10:
            raise ValueError(f"Failed primorial check at q={q}")
        if q > 1024:
            break
    elif q >= 29:
        modulus = q**4
        # 4 log(q) < 16 for q <= 47.
        bound = (16 * q**3 * (q-1))**2
        count = 0
        largest_witness = 0
        for n in range(primorial, bound+1, primorial):
            if n % q:
                p = n % modulus
                while p < n and not is_prime(p):
                    p += modulus
                if p >= n:
                    raise ValueError(f"No verified fourth-power witness for {n}")
                largest_witness = max(p, largest_witness)
                count += 1
        print(q, count, 0, largest_witness)
    else:
        maximum = max_least_prime(q)
        candidates = [n for n in range(primorial, maximum+1, primorial) if n % q]
        bad = [n for n in candidates if not representable(n)]
        exceptions.extend(bad)
        print(q, len(candidates), len(bad), maximum)
    primorial *= q

exceptions.sort()
print("Count:", len(exceptions))
print("Largest:", max(exceptions))
print("Exceptions:", *exceptions)
if (len(exceptions), max(exceptions)) != (811, 1_561_560):
    raise ValueError("Conclusion differs from the stated theorem")
