#!/usr/bin/env python3
"""Finite exact checks for recovery from individual balanced Fourier products.

Run with Python 3.9 or later. No third-party packages, zero tables, or
floating-point arithmetic are used. The dimension-free statements are proved
in the accompanying paper.
"""
from collections import Counter, deque
from functools import lru_cache
from itertools import combinations, combinations_with_replacement
from math import gcd, isqrt, lcm


def divisors(n):
    low = [a for a in range(1, isqrt(n) + 1) if n % a == 0]
    return low + [n // a for a in reversed(low) if n // a != a]


@lru_cache(maxsize=None)
def cyclotomic(n):
    """Return the monic cyclotomic polynomial in ascending coefficient order."""
    poly = [-1] + [0] * (n - 1) + [1]
    for d in divisors(n)[:-1]:
        factor = cyclotomic(d)
        degree = len(factor) - 1
        quotient = [0] * (len(poly) - degree)
        for k in reversed(range(len(quotient))):
            quotient[k] = coefficient = poly[k + degree]
            for j, value in enumerate(factor):
                poly[k + j] -= coefficient * value
        assert not any(poly)
        poly = quotient
    return tuple(poly)


class CyclotomicRing:
    """Exact integer coefficient vectors in Z[X]/Phi_n."""
    def __init__(self, n):
        self.n = n
        self.modulus = cyclotomic(n)
        self.degree = len(self.modulus) - 1
        self.zero = (0,) * self.degree
        self.one = (1,) + self.zero[1:]
        self.roots = [self.one]
        for _ in range(1, n):
            self.roots.append(self.reduce([0] + list(self.roots[-1])))
        assert self.reduce([0] + list(self.roots[-1])) == self.one

    def reduce(self, coefficients):
        coefficients = list(coefficients)
        for i in reversed(range(self.degree, len(coefficients))):
            lead = coefficients[i]
            if lead:
                for j in range(self.degree):
                    coefficients[i - self.degree + j] -= lead * self.modulus[j]
        return tuple((coefficients + [0] * self.degree)[:self.degree])

    @lru_cache(maxsize=65536)
    def multiply(self, a, b):
        coefficients = [0] * (2 * self.degree - 1)
        for i, value in enumerate(a):
            if value:
                for j, other in enumerate(b):
                    coefficients[i + j] += value * other
        return self.reduce(coefficients)

    def fourier(self, histogram, harmonic, offset=0, stride=1):
        """Sum histogram[x] zeta_n^((offset+stride*x)*harmonic)."""
        coefficients = [0] * self.degree
        for x, count in histogram.items():
            root = self.roots[((offset + stride * x) * harmonic) % self.n]
            for j, value in enumerate(root):
                coefficients[j] += count * value
        return tuple(coefficients)

    def product(self, factors):
        result = self.one
        for factor in factors:
            if factor == self.zero:
                return self.zero
            result = self.multiply(result, factor)
        return result


def two_units(d, target):
    """Represent target modulo d as a sum of two units when parity permits."""
    for a in range(1, d):
        b = (target - a) % d
        if gcd(a, d) == gcd(b, d) == 1:
            return (a, b)
    raise ValueError(f"two-unit decomposition unavailable at {(d, target)}")


def unit_sum(d, target):
    """Use a single unit when possible, otherwise at most three."""
    target %= d
    if gcd(d, target) == 1:
        return (target,)
    if d % 2 == 0 and target % 2 == 1:
        return (1,) + two_units(d, target - 1)
    return two_units(d, target)


def fixed_schedule(n):
    """Map a singleton/pair of divisor layers to its balanced residues."""
    schedule = {}
    ds = divisors(n)[1:]
    for d in ds:
        if d == 2:
            units = (1, -1)
        elif d % 2:
            units = (1, 1, -2)
        elif d % 3:
            units = (1, 1, 1, -3)
        else:
            units = (1, 1, 1, 1) + two_units(d, -4)
        schedule[(d,)] = tuple(u * (n // d) % n for u in units)
    for d, e in combinations(ds, 2):
        g = gcd(d, e)
        if g == 1:
            continue
        left = tuple(u * (n // d) % n for u in unit_sum(d, d // g))
        right = tuple(u * (n // e) % n for u in unit_sum(e, -e // g))
        schedule[(d, e)] = left + right
    return schedule


def audit_schedule(n):
    schedule = fixed_schedule(n)
    for label, slots in schedule.items():
        assert sum(slots) % n == 0 and all(slots)
        assert {n // gcd(n, k) for k in slots} == set(label)
        assert 2 <= len(slots) <= (4 if n % 2 else 6)
        if len(label) == 2:
            d, e = label
            intersection = gcd(d, e)
            for layer, sign in ((d, 1), (e, -1)):
                charge = sum(k for k in slots if n // gcd(n, k) == layer)
                assert (charge - sign * (n // intersection)) % n == 0
    return schedule


def canonical_rotation(n, positions):
    return min(tuple(sorted((x + shift) % n for x in positions))
               for shift in range(n))


def probe_values(ring, histogram, schedule):
    active_harmonics = {k for slots in schedule.values() for k in slots}
    fourier = {k: ring.fourier(histogram, k) for k in active_harmonics}
    return {label: ring.product(fourier[k] for k in slots)
            for label, slots in schedule.items()}


def anchor_slots(n, active, g):
    """Build a sum of old active harmonics having residue -n/g."""
    # When one active layer contains the target, at most three factors suffice.
    for d in active:
        if d % g == 0:
            return tuple((n // d) * u % n for u in unit_sum(d, -d // g))

    # A shortest-path search is enough for these small checks. Bezout's
    # identity proves existence at arbitrary modulus, as used in the paper.
    target = (-n // g) % n
    steps = [(sign * n // d) % n for d in active for sign in (1, -1)]
    queue = deque([0])
    paths = {0: ()}
    while queue:
        here = queue.popleft()
        for k in steps:
            there = (here + k) % n
            if there not in paths:
                paths[there] = paths[here] + (k,)
                if there == target:
                    return paths[there]
                queue.append(there)
    raise AssertionError("target lies outside the old subgroup")


def adaptive_transcript(ring, histogram, schedule):
    """Run a deterministic strategy using exactly one query for each layer."""
    n = ring.n
    active = []
    period = 1
    fourier = {}
    transcript = []
    for d in reversed(divisors(n)[1:]):
        g = gcd(d, period)
        slots = schedule[(d,)] if g == 1 else (
            (n // d,) * (d // g) + anchor_slots(n, active, g)
        )
        assert sum(slots) % n == 0
        for k in slots:
            if k not in fourier:
                fourier[k] = ring.fourier(histogram, k)
        answer = ring.product(fourier[k] for k in slots)
        transcript.append((slots, answer))
        if answer != ring.zero:
            active.append(d)
            period = lcm(period, d)
    return tuple(transcript)


def exhaustive(n, mass):
    """Check equality of exact measurement keys iff translated, for this mass."""
    ring = CyclotomicRing(n)
    schedule = audit_schedule(n)
    by_measurement, by_orbit, by_transcript = {}, {}, {}
    sample_count = 0
    for points in combinations_with_replacement(range(n), mass):
        histogram = Counter(points)
        key = tuple(probe_values(ring, histogram, schedule).values())
        transcript = adaptive_transcript(ring, histogram, schedule)
        orbit = canonical_rotation(n, points)
        assert by_measurement.setdefault(key, orbit) == orbit
        assert by_orbit.setdefault(orbit, (key, transcript)) == (key, transcript)
        assert by_transcript.setdefault(transcript, orbit) == orbit
        sample_count += 1
    print(f"  E={n:2}, m={mass}: {sample_count:4} histograms, "
          f"{len(by_orbit):3} rotation classes, {len(by_measurement):3} fixed keys, "
          f"{len(by_transcript):3} adaptive transcripts")


def ramanujan(d, x):
    # The trace over primitive d-th roots is rational integral. Compute it in
    # the cyclotomic basis instead of using the closed Ramanujan-sum formula.
    ring = ramanujan_ring(d)
    trace = tuple(sum(ring.roots[(a*x) % d][j] for a in range(1, d)
                      if gcd(a, d) == 1) for j in range(ring.degree))
    assert not any(trace[1:])
    return trace[0]


@lru_cache(maxsize=None)
def ramanujan_ring(d):
    return CyclotomicRing(d)


def edge_obstructions():
    n = 30
    ring = CyclotomicRing(n)
    schedule = audit_schedule(n)
    ds = divisors(n)[1:]
    traces = {d: [ramanujan(d, x) for x in range(n)] for d in ds}
    # Choose one common known mass across every uniform and two-layer witness.
    baseline = 2 * n
    uniform = {x: baseline for x in range(n)}
    base_key = probe_values(ring, uniform, schedule)
    for d in ds:
        f = {x: baseline + traces[d][x] for x in range(n)}
        key = probe_values(ring, f, schedule)
        assert [k for k in base_key if base_key[k] != key[k]] == [(d,)]
    for d, e in (k for k in schedule if len(k) == 2):
        f = {x: baseline + traces[d][x] + traces[e][x] for x in range(n)}
        h = {x: baseline + traces[d][x] + traces[e][(x-1) % n]
             for x in range(n)}
        assert all(v > 0 for v in list(f.values()) + list(h.values()))
        assert sum(f.values()) == sum(h.values()) == baseline * n
        assert not any(all(f[(x-t) % n] == h[x] for x in range(n))
                       for t in range(n))
        fk = probe_values(ring, f, schedule)
        hk = probe_values(ring, h, schedule)
        assert [k for k in fk if fk[k] != hk[k]] == [(d, e)]
        if (d,e) == (6,10):
            slots = schedule[(d,e)]
            print(f"  E=30, mixed layers (6,10), slots={slots}, mass={sum(f.values())}")
            print(f"    F-probe = {fk[(d,e)][0]}, shifted probe = {hk[(d,e)][0]}")
    print(f"  All {len(ds)} singleton and {len(schedule)-len(ds)} mixed "
          "witnesses separate only on their designated fixed probe.")


def degree_five_obstruction():
    n = 6
    ring = CyclotomicRing(n)
    f = {x: 9 + 2*ramanujan(6,x) + ramanujan(6,x-1) for x in range(n)}
    h = {x: 9 + 2*ramanujan(6,x) + ramanujan(6,x+1) for x in range(n)}
    assert not any(all(f[(x-t) % n] == h[x] for x in range(n)) for t in range(n))
    fk = [ring.fourier(f, k) for k in range(n)]
    hk = [ring.fourier(h, k) for k in range(n)]
    probes = 0
    for r in range(1,6):
        for slots in combinations_with_replacement(range(n), r):
            if sum(slots) % n == 0:
                assert ring.product(fk[k] for k in slots) == ring.product(hk[k] for k in slots)
                probes += 1
    assert ring.product([fk[1]]*6) != ring.product([hk[1]]*6)
    print(f"  E=6: {probes} balanced multisets of 1–5 harmonics agree, (1,)*6 differs.")


def dirichlet_factor():
    # Characters modulo 61: choose the primitive root 2.  Take twists of the
    # order-60 character psi by all powers of its square. Every psi^(1+2x)
    # is nonprincipal and hence primitive modulo 61.
    assert {pow(2,k,61) for k in range(60)} == set(range(1,61))
    n = 30
    ring = CyclotomicRing(60)
    hist = {0: 1, 1: 2, 7: 3, 24: 1}
    schedule = audit_schedule(n)
    for slots in schedule.values():
        lifted = list(slots)
        lifted[-1] -= sum(lifted)
        assert sum(lifted) == 0 and all(lifted)
        with_base = ring.product(ring.fourier(hist, k, offset=1, stride=2)
                                for k in lifted)
        without_base = ring.product(ring.fourier(hist, k, stride=2)
                                   for k in lifted)
        assert with_base == without_base
    print("  Q=61, p=2, E=30: base character cancels for all "
          f"{len(schedule)} signed integer lifts.")


def main():
    print("Finite exact checks of cyclotomic probes")
    for n in range(2,301):
        audit_schedule(n)
    print("  Verified divisor supports, total balance, and intersection charges for 2 <= E <= 300.")
    print("Selected schedule sizes (support, bridge, maximum degree)")
    for n in (3, 6, 9, 15, 27, 30, 45, 60, 81, 210):
        schedule = audit_schedule(n)
        pure = sum(len(s) == 1 for s in schedule)
        print(f"  E={n:3}: {pure:2} + {len(schedule)-pure:2}, "
              f"degree <= {max(map(len,schedule.values()))}")
    print("Exhaustive equal-mass classifications, exact cyclotomic coefficients")
    for n,m in ((3,6), (4,5), (6,5), (8,4), (9,4), (12,4), (15,3)):
        exhaustive(n,m)
    print("Support-specific lower-bound witnesses")
    edge_obstructions()
    degree_five_obstruction()
    print("Finite Dirichlet character identity")
    dirichlet_factor()
    print("All checks passed.")


if __name__ == "__main__":
    main()
