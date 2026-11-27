"""Exact finite checks of the adaptive, bounded-order one-prime protocol.

Uses only the Python standard library.  No floating-point approximation enters
the finite transcript.  Frequencies are residues mod E and checks are over Z[x]/Phi_E.
"""
import json
from collections import Counter
from functools import cache
from itertools import combinations_with_replacement, product
from math import gcd, lcm


@cache
def divisors(n):
    return tuple(d for d in range(1, n + 1) if n % d == 0)


def primary_powers(n):
    result = []
    for p in divisors(n):
        if p == 1 or len(divisors(p)) != 2:
            continue
        q = p
        while n % (q * p) == 0:
            q *= p
        result.append(q)
    return result


@cache
def two_units(n, target):
    for u in range(1, n):
        v = (target - u) % n
        if gcd(u, n) == gcd(v, n) == 1:
            return (u, v)
    raise ValueError((n, target))


def unit_sum(n, target):
    target %= n
    if gcd(target, n) == 1:
        return (target,)
    if n % 2 == 0 and target % 2:
        return (1,) + two_units(n, (target - 1) % n)
    return two_units(n, target)


@cache
def probe(E, old, d):
    g = gcd(d, lcm(*old))
    h = d // g
    k = 3 if d % 2 or h % 2 else 4
    local = (1,) * k + two_units(d, (h - k) % d)
    slots = [u * (E // d) for u in local]
    assert sum(local) % d == h % d
    assert all(gcd(u, d) == 1 for u in local)
    for q in primary_powers(g):
        anchor = next(e for e in old if e % q == 0)
        a = -pow(g // q, -1, q)
        residues = unit_sum(anchor, a * (anchor // q))
        slots.extend(u * (E // anchor) for u in residues)
    assert sum(slots) % E == 0
    assert len(slots) <= 6 + 3 * len(primary_powers(g))
    assert set(E // gcd(E, s) for s in slots[len(local):]).issubset(old)
    # Among translations of shell d, those preserving the local value are
    # exactly the translations fixing the old nonzero coefficients.
    assert {j for j in range(d) if j * sum(local) % d == 0} == {
        t % d for t in range(0, E, lcm(*old))
    }
    return tuple(slots)


def divide_monic(f, g):
    f = list(f)
    quotient = [0] * (len(f) - len(g) + 1)
    for j in reversed(range(len(quotient))):
        quotient[j] = f[j + len(g) - 1]
        for k, a in enumerate(g):
            f[j + k] -= quotient[j] * a
    assert not any(f)
    return tuple(quotient)


@cache
def cyclotomic(n):
    f = (-1,) + (0,) * (n - 1) + (1,)
    for d in divisors(n)[:-1]:
        f = divide_monic(f, cyclotomic(d))
    return f


def reduce_poly(coefficients, modulus):
    coefficients = list(coefficients)
    r = len(modulus) - 1
    for j in reversed(range(r, len(coefficients))):
        lead = coefficients[j]
        if lead:
            for k in range(r):
                coefficients[j - r + k] -= lead * modulus[k]
    return tuple((coefficients + [0] * r)[:r])


@cache
def multiply(a, b, modulus):
    c = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i + j] += x * y
    return reduce_poly(c, modulus)


def transcripts(E, m):
    order = divisors(E)[:0:-1]
    poly = cyclotomic(E)
    one = reduce_poly([1], poly)
    seen = {}
    count = 0
    for multiset in combinations_with_replacement(range(E), m):
        counts = Counter(multiset)
        histogram = tuple(counts[j] for j in range(E))
        orbit = min(histogram[j:] + histogram[:j] for j in range(E))
        fourier = {}
        old = ()
        observations = []
        for d in order:
            slots = probe(E, old, d)
            value = one
            for s in slots:
                if s not in fourier:
                    f = [0] * E
                    for t in multiset:
                        f[s * t % E] += 1
                    fourier[s] = reduce_poly(f, poly)
                value = multiply(value, fourier[s], poly)
            observations.append(value)
            if any(value):
                old += (d,)
            assert any(value) == any(fourier[E // d])
        key = tuple(observations)
        assert seen.setdefault(key, orbit) == orbit
        count += 1
    assert len(set(seen.values())) == len(seen)
    return {"E": E, "mass": m, "histograms": count, "rotation_classes": len(seen)}


def main():
    # Test every support and every prospective new class, including cases with
    # several CRT anchors.  The order of probing the active classes is immaterial.
    cases = 0
    max_length = 0
    examples = list(range(2, 81)) + [105, 210, 315, 385]
    for E in examples:
        orders = divisors(E)[1:]
        for d in orders:
            others = tuple(e for e in orders if e != d)
            for flags in product((False, True), repeat=len(others)):
                old = tuple(e for e, flag in zip(others, flags) if flag)
                slots = probe(E, old, d)
                max_length = max(max_length, len(slots))
                cases += 1
    tests = [transcripts(E, 4) for E in (2, 3, 4, 6, 8, 9, 10, 12, 15)]
    print(json.dumps({"support_steps": cases, "largest_row_seen": max_length,
                      "exact_transcripts": tests}, indent=2))


if __name__ == "__main__":
    main()
