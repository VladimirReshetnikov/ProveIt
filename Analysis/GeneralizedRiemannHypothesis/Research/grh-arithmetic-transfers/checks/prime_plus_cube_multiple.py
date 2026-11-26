"""Classify sums of a prime and a positive multiple of a prime cube."""
from math import isqrt, prod


def sieve(limit):
    prime = bytearray(b"\1") * (limit + 1)
    prime[:2] = b"\0\0"
    for p in range(2, isqrt(limit) + 1):
        if prime[p]:
            prime[p*p::p] = bytes((limit - p*p)//p + 1)
    return prime


flags = sieve(25_000_000)
primes = [p for p in range(2, len(flags)) if flags[p]]
small = [p for p in primes if p <= 41]

# Beyond 257 induction and Bertrand's postulate give the same inequality.
for q in (p for p in primes if 43 <= p <= 257):
    assert prod(p for p in primes[:60] if p < q) > 9*q**8

# Bound all possible exceptions using first primes for the least prime q
# missing from n. For n >= primorial_below_q, a check is required only if
# that primorial does not already exceed the largest least prime.
bound = 0
primorial_below_q = 1
print("q,maximum_least_prime,primorial_below_q")
for q in small:
    modulus = q**3
    covered = bytearray(modulus)
    missing = modulus - modulus//q
    for r in primes:
        a = r % modulus
        if a % q and not covered[a]:
            covered[a] = 1
            missing -= 1
            if not missing:
                break
    assert not missing
    print(f"{q},{r},{primorial_below_q}")
    if r >= primorial_below_q:
        bound = max(bound, r)
    primorial_below_q *= q

# Complete search on the remaining interval, including primes dividing n.
possible = bytearray(bound + 1)
for q in primes:
    cube = q**3
    if cube + 2 > bound:
        break
    for a in range(cube):
        # In a given class, the first prime r supplies all n = r + k*cube
        # for k >= 1. This includes classes that are not units.
        r = a
        while r + cube <= bound and not flags[r]:
            r += cube
        first = r + cube
        if first <= bound:
            possible[first::cube] = bytes([1])*((bound-first)//cube+1)
exceptions = [n for n in range(1, bound + 1) if not possible[n]]
print("exhaustive_bound", bound)
print("exceptions", len(exceptions), exceptions)

# Independently check every exception by subtracting each positive
# multiple of every prime cube and testing primality directly.
for n in exceptions:
    for q in primes:
        cube = q**3
        if cube + 2 > n:
            break
        assert not any(flags[n-s] for s in range(cube, n-1, cube))

# An independent check of the full finite classification. Construct the
# cube multiples directly using every integer base, then form the sumset
# by bit shifts, one shift for each possible prime summand.
cube_multiples = bytearray(bound//8 + 1)
d = 2
while d**3 <= bound:
    for m in range(d**3, bound + 1, d**3):
        cube_multiples[m//8] |= 1 << (m % 8)
    d += 1
multiples = int.from_bytes(cube_multiples, "little")
sums = 0
for p in primes:
    if p + 8 > bound:
        break
    sums |= multiples << p
represented = sums.to_bytes((sums.bit_length()+7)//8, "little")
assert exceptions == [n for n in range(1, bound+1)
                      if not (represented[n//8] >> (n%8)) & 1]
print("independent sumset agrees for every n through", bound)

# A cube multiple is also a square multiple. Only the 62 exceptions need
# a second test to recover the sharp square theorem.
square_exceptions = []
for n in exceptions:
    witness = None
    for q in primes:
        if q*q + 2 > n:
            break
        for p in range(n - q*q, 1, -q*q):
            if flags[p]:
                witness = (p, q)
                break
        if witness:
            break
    if witness is None:
        square_exceptions.append(n)
assert square_exceptions == [1, 2, 3, 4, 5, 8, 24]
print("square exceptions among positive integers:", square_exceptions)
