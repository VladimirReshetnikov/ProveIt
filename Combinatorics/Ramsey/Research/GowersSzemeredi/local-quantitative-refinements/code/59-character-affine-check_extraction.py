#!/usr/bin/env python3
"""Exact finite checks for character separation and Freiman extraction.

All computations use integers.  The general results are proved analytically
in the companion research article; these finite checks are supplementary.
Run without -O: assertions are part of this verifier.
"""

from collections import defaultdict
from fractions import Fraction
from itertools import product
from math import comb, gcd, lcm
import json

if not __debug__:
    raise SystemExit("Run without -O or -OO; assertions are required.")


def floor_log(base, n):
    assert base >= 2 and n >= 1
    ans, power = 0, 1
    while power * base <= n:
        power *= base
        ans += 1
    return ans


def rank_bound(q, odd=False, primary=None):
    if primary is not None:
        return floor_log(primary, (primary - 1) * q + 1)
    return floor_log(3, 2 * q + 1) if odd else floor_log(2, q + 1)


class FiniteGroup:
    def __init__(self, moduli):
        self.moduli = tuple(moduli)
        self.elements = list(product(*(range(n) for n in moduli)))
        self.zero = (0,) * len(moduli)
        self.exponent = lcm(*moduli)
        self.reps = sorted({min(x, self.neg(x)) for x in self.elements
                            if x != self.zero})
        self.orbit_index = {x: j for j, x in enumerate(self.reps)}
        self.odd = all(n % 2 for n in moduli)

    def neg(self, x):
        return tuple(-a % n for a, n in zip(x, self.moduli))

    def sub(self, x, y):
        return tuple((a - b) % n for a, b, n in zip(x, y, self.moduli))

    def add_many(self, xs):
        return tuple(sum(x[i] for x in xs) % n
                     for i, n in enumerate(self.moduli))

    def order(self, x):
        return lcm(*(n // gcd(a, n) for a, n in zip(x, self.moduli)))

    def evaluate(self, char, x):
        """Return E * chi(x) modulo E, where E is the exponent."""
        return sum(a * b * (self.exponent // n)
                   for a, b, n in zip(char, x, self.moduli)) % self.exponent

    def covers(self, denominator):
        out = []
        for char in self.elements:
            mask = 0
            for j, x in enumerate(self.reps):
                v = self.evaluate(char, x)
                if min(v, self.exponent - v) * denominator >= self.exponent:
                    mask |= 1 << j
            out.append((char, mask))
        return out

    def defect_mask(self, defects):
        mask = 0
        for x in defects:
            if x != self.zero:
                rep = min(x, self.neg(x))
                mask |= 1 << self.orbit_index[rep]
        return mask


def greedy_separator(group, forbidden_mask, odd=False, primary=None):
    base, denominator = ((primary, 2 * primary) if primary is not None else
                         ((3, 7) if odd else (2, 5)))
    q = forbidden_mask.bit_count()
    m = rank_bound(q, odd, primary)
    covers = group.covers(denominator)
    survivors, chosen = forbidden_mask, []
    while survivors:
        before = survivors.bit_count()
        char, cover = min(covers,
                          key=lambda z: (survivors & ~z[1]).bit_count())
        survivors &= ~cover
        # Strict averaging, including the common zero-character event.
        assert base * survivors.bit_count() < before
        chosen.append(char)
    assert len(chosen) <= m
    for j, x in enumerate(group.reps):
        if forbidden_mask & (1 << j):
            assert any(min(group.evaluate(c, x),
                           group.exponent - group.evaluate(c, x))
                       * denominator >= group.exponent for c in chosen)
    return chosen


def check_arithmetic():
    count = 0
    for n in range(2, 100001):
        small = 2 * ((n + 4) // 5) - 1
        assert 2 * small <= n
        count += 1
    for n in range(3, 100001, 2):
        small = 2 * ((n + 6) // 7) - 1
        assert 3 * small <= n
        count += 1
    cutoff_checks = 0
    for ell in (3, 5, 7, 9, 11, 13, 17, 31):
        denominator = 3 * ell - 2
        for n in range(ell, 20002, 2):
            small = 2 * ((n + denominator - 1) // denominator) - 1
            assert ell * small <= n
            cutoff_checks += 1
    for q in range(100001):
        for base, odd in ((2, False), (3, True)):
            n, steps = q, 0
            while n:
                n = (n - 1) // base
                steps += 1
            assert steps == rank_bound(q, odd)
    for p in (2, 3, 5, 7, 11, 13, 17, 19):
        for a in range(1, 10):
            n = p ** a
            small = 2 * ((n + 2 * p - 1) // (2 * p)) - 1
            assert p * small <= n
            if p % 2:
                assert p * small == n
        for q in range(10001):
            n, steps = q, 0
            while n:
                n = (n - 1) // p
                steps += 1
            assert steps == rank_bound(q, primary=p)
    # Sharp universal-radius obstructions with the optimal number of chars.
    sharp = {}
    for p in (5, 7):
        group = FiniteGroup((p,))
        best = max(min(Fraction(min(group.evaluate(c, x),
                                   p - group.evaluate(c, x)), p)
                       for x in group.reps) for c in group.elements)
        assert best == Fraction(1, p)
        sharp[p] = str(best)
    return {"small_ball_checks": count,
            "torsion_cutoff_checks": cutoff_checks,
            "recurrence_inputs": 100001,
            "sharp_radius_examples": sharp}


def check_all_forbidden_sets():
    groups = [(2,), (3,), (4,), (5,), (6,), (7,), (8,), (9,), (10,),
              (12,), (2, 2), (2, 3), (3, 3), (2, 2, 2)]
    records = []
    for moduli in groups:
        group = FiniteGroup(moduli)
        counts = {"universal": 0, "odd": 0}
        for mask in range(1 << len(group.reps)):
            greedy_separator(group, mask)
            counts["universal"] += 1
            if group.odd:
                greedy_separator(group, mask, odd=True)
                counts["odd"] += 1
        records.append({"moduli": moduli, "sign_orbits": len(group.reps),
                        "forbidden_sets_checked": counts})
    return records


def check_primary_forbidden_sets():
    records = []
    cases = [(2, (2,)), (2, (4,)), (2, (8,)), (2, (2, 2, 2)),
             (3, (3,)), (3, (9,)), (3, (3, 3)), (5, (5,)),
             (5, (25,)), (5, (5, 5)), (7, (7,))]
    for p, moduli in cases:
        group = FiniteGroup(moduli)
        count = 0
        for mask in range(1 << len(group.reps)):
            greedy_separator(group, mask, primary=p)
            count += 1
        records.append({"prime": p, "moduli": moduli,
                        "forbidden_sets_checked": count})
    return records


def k_sums(domain, values, modulus, group, k):
    buckets = defaultdict(set)
    for indices in product(range(len(domain)), repeat=k):
        x_sum = sum(domain[i] for i in indices) % modulus
        y_sum = group.add_many([values[i] for i in indices])
        buckets[x_sum].add(y_sum)
    return buckets


def verify_freiman(domain, values, modulus, group, k):
    for j in range(1, k + 1):
        assert all(len(ys) == 1
                   for ys in k_sums(domain, values, modulus, group, j).values())


def extract_and_check(domain, values, modulus, group, k, odd=False, primary=None):
    buckets = k_sums(domain, values, modulus, group, k)
    defects = {group.sub(a, b) for ys in buckets.values()
               for a, b in product(ys, repeat=2)} - {group.zero}
    assert defects == {group.neg(x) for x in defects}
    mask = group.defect_mask(defects)
    chars = greedy_separator(group, mask, odd=odd, primary=primary)
    m = rank_bound(mask.bit_count(), odd, primary)
    denominator = 2 * primary if primary is not None else (7 if odd else 5)
    number_of_arcs = denominator * k
    cells = defaultdict(list)
    exact_cells = defaultdict(list)
    for i, y in enumerate(values):
        key = tuple(number_of_arcs * group.evaluate(c, y) // group.exponent
                    for c in chars)
        cells[key].append(i)
        exact_key = tuple(group.evaluate(c, y) for c in chars)
        exact_cells[exact_key].append(i)
    assert len(cells) <= min(group.exponent, number_of_arcs) ** len(chars)
    indices = max(cells.values(), key=len)
    assert len(indices) * min(group.exponent, number_of_arcs) ** m >= len(domain)
    verify_freiman([domain[i] for i in indices], [values[i] for i in indices],
                   modulus, group, k)
    exact_indices = max(exact_cells.values(), key=len)
    assert len(exact_indices) * group.exponent ** m >= len(domain)
    verify_freiman([domain[i] for i in exact_indices],
                   [values[i] for i in exact_indices], modulus, group, k)


def check_extraction():
    counts = []
    cases = [(4, (2,), 2), (4, (3,), 2), (4, (5,), 2),
             (4, (2, 2), 2), (3, (3,), 3), (3, (2, 2), 3)]
    for modulus, moduli, k in cases:
        group = FiniteGroup(moduli)
        count = odd_count = primary_count = 0
        p = moduli[0]
        for mask in range(1, 1 << modulus):
            domain = [x for x in range(modulus) if mask & (1 << x)]
            for values in product(group.elements, repeat=len(domain)):
                extract_and_check(domain, values, modulus, group, k)
                count += 1
                if group.odd:
                    extract_and_check(domain, values, modulus, group, k, odd=True)
                    odd_count += 1
                extract_and_check(domain, values, modulus, group, k, primary=p)
                primary_count += 1
        counts.append({"domain_modulus": modulus, "target_moduli": moduli,
                       "order": k, "maps_checked": count,
                       "odd_maps_checked": odd_count,
                       "primary_maps_checked": primary_count})
    return counts


def check_rank_obstructions():
    out = []
    for p in (2, 3, 5):
        for m in range(3):
            group = FiniteGroup((p,) * (m + 1))
            denominator = 5 if p == 2 else (7 if p == 3 else 2 * p)
            masks = [mask for _, mask in group.covers(denominator)]
            projective = set()
            for x in group.elements:
                if x == group.zero:
                    continue
                first = next(a for a in x if a)
                inverse = pow(first, -1, p)
                projective.add(tuple(a * inverse % p for a in x))
            full = group.defect_mask(projective)
            assert full.bit_count() == (p ** (m + 1) - 1) // (p - 1)
            assert rank_bound(full.bit_count(), primary=p) == m + 1
            checked = 0
            for selected in product(masks, repeat=m):
                union = 0
                for mask in selected:
                    union |= mask
                assert union != full
                checked += 1
            out.append({"prime": p, "available_characters": m,
                        "dimension": m + 1, "sign_orbits": full.bit_count(),
                        "character_tuples_checked": checked})
    return out


def check_riesz_constants():
    """Integer Laurent coefficients; no floating-point trigonometry."""
    def multiply(left, right, modulus=None):
        out = defaultdict(int)
        for a, ca in left.items():
            for b, cb in right.items():
                exponent = a + b
                if modulus is not None:
                    exponent %= modulus
                out[exponent] += ca * cb
        return {a: ca for a, ca in out.items() if ca}

    constants = []
    torsion_product_checks = deleted_product_checks = 0
    for ell in range(1, 17):
        # (2-z-z^(-1))^ell = 2^ell (1-cos(theta))^ell.
        polynomial = {0: 1}
        for _ in range(ell):
            polynomial = multiply(polynomial, {-1: -1, 0: 2, 1: -1})
        assert polynomial[0] == comb(2 * ell, ell)
        assert min(polynomial) == -ell and max(polynomial) == ell
        constants.append(str(Fraction(polynomial[0], 2 ** ell)))
        if ell > 6:
            continue
        for q in range(1, 4):
            radix = ell + 1
            modulus = radix ** q
            frequencies = [radix ** j for j in range(q)]
            # These digits are ell-dissociated modulo radix^q.
            for coefficients in product(range(-ell, ell + 1), repeat=q):
                if any(coefficients):
                    assert sum(a * f for a, f in zip(coefficients, frequencies)) % modulus
            for deleted in [None] + list(range(q)):
                combined = {0: 1}
                included = 0
                for j, frequency in enumerate(frequencies):
                    if j == deleted:
                        continue
                    factor = defaultdict(int)
                    for exponent, coefficient in polynomial.items():
                        factor[exponent * frequency % modulus] += coefficient
                    combined = multiply(combined, factor, modulus)
                    included += 1
                assert combined.get(0, 0) == polynomial[0] ** included
                if deleted is None:
                    torsion_product_checks += 1
                else:
                    deleted_product_checks += 1
    return {"ell_range": [1, 16], "normalized_constants": constants,
            "finite_cyclic_full_products": torsion_product_checks,
            "finite_cyclic_deleted_products": deleted_product_checks,
            "cyclic_test_family": "ell=1..6, q=1..3; C_((ell+1)^q), D={(ell+1)^j:0<=j<q}"}


if __name__ == "__main__":
    report = {"scope": "Supplementary exact finite checks; not a proof of generality",
              "arithmetic": check_arithmetic(),
              "all_forbidden_sets": check_all_forbidden_sets(),
              "primary_forbidden_sets": check_primary_forbidden_sets(),
              "freiman_extraction": check_extraction(),
              "sharp_rank_obstructions": check_rank_obstructions(),
              "riesz_constants": check_riesz_constants(),
              "status": "all exact checks passed"}
    print(json.dumps(report, indent=2, sort_keys=True))
