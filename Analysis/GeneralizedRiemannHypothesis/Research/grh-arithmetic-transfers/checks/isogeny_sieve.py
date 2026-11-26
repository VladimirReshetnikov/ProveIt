"""Verify the cubic local sieve and construct a sharp A4 sextic example.

Standard library. Run beside the supplied sextic_parameter.txt to verify it.
Use --write-parameter to regenerate the rational CRT parameter.
"""
import argparse
from collections import Counter
from itertools import combinations, permutations
from hashlib import sha256
from math import gcd, isqrt
from pathlib import Path
import sys

P = 253507
BASE = Path(__file__).resolve().parent
if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)


def prime_list(limit):
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = bytes(2)
    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            sieve[p*p::p] = bytes((limit - p*p)//p + 1)
    return [p for p in range(2, limit + 1) if sieve[p]]


def splits(q, p):
    return pow(q, (p - 1)//2, p) == 1


def survives(p, auxiliaries):
    for q in auxiliaries:
        if 4*q**3 >= p:
            break
        if splits(q, p) and (q*q + q + 1) % p and (q**6 + q**3 + 1) % p:
            return False
    return True


def cycle_type(permutation):
    visited = set()
    lengths = []
    for i in range(len(permutation)):
        if i in visited:
            continue
        start = i
        length = 0
        while i not in visited:
            visited.add(i)
            length += 1
            i = permutation[i]
        assert i == start
        lengths.append(length)
    return tuple(sorted(lengths))


def even_permutations(n):
    for g in permutations(range(n)):
        if sum(g[i] > g[j] for i, j in combinations(range(n), 2)) % 2 == 0:
            yield g


def compose(g, h):
    return tuple(g[i] for i in h)


def sylow_fives(group):
    subgroups = set()
    for g in group:
        if cycle_type(g) == (5,):
            elt = tuple(range(5))
            subgroup = []
            for _ in range(5):
                subgroup.append(elt)
                elt = compose(g, elt)
            subgroups.add(frozenset(subgroup))
    return sorted(subgroups, key=lambda h: sorted(h))


def check_actions():
    edges = list(combinations(range(4), 2))
    tetrahedron = Counter()
    for g in even_permutations(4):
        induced = [edges.index(tuple(sorted((g[x], g[y])))) for x, y in edges]
        tetrahedron[cycle_type(induced)] += 1

    group = list(even_permutations(5))
    subgroups = sylow_fives(group)
    assert len(subgroups) == 6
    icosahedron = Counter()
    for g in group:
        inv = tuple(g.index(i) for i in range(5))
        action = []
        for h in subgroups:
            image = frozenset(compose(compose(g, x), inv) for x in h)
            action.append(subgroups.index(image))
        icosahedron[cycle_type(action)] += 1
    assert all(any(f in (1, 3) for f in shape)
               for shape in set(tetrahedron) | set(icosahedron))
    print("A4 edge cycle types", dict(sorted(tetrahedron.items())))
    print("A5 Sylow-5 action cycle types", dict(sorted(icosahedron.items())))


def mul(x, y, t, q):
    """Multiply in F_q[X]/(X^3-tX^2-(t+3)X-1)."""
    coeff = [0]*5
    for i, a in enumerate(x):
        for j, b in enumerate(y):
            coeff[i+j] += a*b
    for i in (4, 3):
        c = coeff[i]
        coeff[i-1] += t*c
        coeff[i-2] += (t+3)*c
        coeff[i-3] += c
    return tuple(c % q for c in coeff[:3])


def irreducible(t, q):
    if q == 2:
        return all((x**3 - t*x*x - (t+3)*x - 1) % 2 for x in (0, 1))
    # In odd characteristic a separable cubic with square discriminant
    # either splits or is irreducible.
    if (t*t + 3*t + 9) % q == 0:
        return False
    x = (0, 1, 0)
    power = x
    value = (1, 0, 0)
    exponent = q
    while exponent:
        if exponent & 1:
            value = mul(value, power, t, q)
        power = mul(power, power, t, q)
        exponent //= 2
    return value != x


def crt_parameter(targets, split_prime=17):
    # At the auxiliary prime prescribe the base polynomial mod its square.
    # For the endpoint model the prime is 17 and the chosen root is 3.
    modulus, t = split_prime**2, 0
    for q in targets:
        # Spread prescribed residues evenly across the primes to keep the
        # rational reconstruction from repeatedly selecting the same fraction.
        seed = int.from_bytes(sha256(str(q).encode()).digest(), "big") % q
        residue = next((seed+i) % q for i in range(q)
                       if irreducible((seed+i) % q, q))
        step = ((residue - t) * pow(modulus, -1, q)) % q
        t += step * modulus
        modulus *= q
    # The pairs (r,b) produced by Euclid satisfy r = t*b mod modulus.
    # Near sqrt(modulus), both coordinates can be much shorter than t.
    r0, r1, b0, b1 = modulus, t, 0, 1
    bound = isqrt(modulus)
    while r1 > bound:
        quot, rem = divmod(r0, r1)
        r0, r1 = r1, rem
        b0, b1 = b1, b0 - quot*b1
    for offset in range(100):
        a, b = r1 + offset*r0, b1 + offset*b0
        if gcd(a, b) == 1 and gcd(b, modulus) == 1:
            if b < 0:
                a, b = -a, -b
            assert (a - t*b) % modulus == 0
            return a, b
    raise ArithmeticError("No coprime short reconstruction found.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write-parameter', action='store_true')
    args = parser.parse_args()
    check_actions()
    primes = prime_list(P)
    assert primes[-1] == P
    eligible = [p for p in primes if p % 4 == 3 and survives(p, primes)]
    print("survivors up to", P, "count", len(eligible))
    print(*eligible, sep=", ")
    assert eligible[-1] == P
    targets = [q for q in primes if 4*q < P and splits(q, P)]
    assert all(4*q**3 >= P for q in targets)
    print("primes forced inert", len(targets), "smallest", min(targets),
          "largest", max(targets))
    filename = BASE / "sextic_parameter.txt"
    if args.write_parameter:
        a, b = crt_parameter(targets)
        filename.write_text(f"{a}\n{b}\n")
    else:
        a, b = map(int, filename.read_text().split())
    assert gcd(a, b) == 1 and a % 289 == 0 and b % 17 != 0
    assert all(irreducible(a * pow(b, -1, q) % q, q) for q in targets)
    print("largest integer polynomial coefficient, decimal digits",
          max(len(str(abs(v))) for v in (b, a, a+3*b)))
    print("largest coefficient for monic polynomial of B*alpha, decimal digits",
          max(len(str(abs(v))) for v in (a, b*(a+3*b), b**3)))
    print("f_0(X) roots modulo 17", [u for u in range(17) if
                                        (u**3 - 3*u - 1) % 17 == 0])
    assert (b*(3**3 - 3*3 - 1) - a*(3**2 + 3)) % 289 == (17*b) % 289
    print("all checks passed")


if __name__ == "__main__":
    main()
