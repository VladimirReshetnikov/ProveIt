#!/usr/bin/env python3
"""Exact finite checks for the overlap-energy manuscript (standard library).

This program checks identities and statements on finite examples. It is not a
proof of the universal theorems. Default enumeration covers all nonempty sets
in cyclic groups of orders 2..16 and eight noncyclic groups of orders at most 16.
Mixed identities are checked for every ordered nonempty pair in the specified
groups of orders at most 9; a shift of the second set is another enumerated
pair, so this includes every translated instance.
Run from the package root with:
    python code/verify_energy.py
    python code/verify_energy.py --weights-only
Default JSON destinations are the package data/energy_checks.json and
package data/weighted_energy_checks.json, respectively. Override with --output.
Absolute script paths may be used from another working directory; the default
output paths still resolve to this package. Only the Python standard library
is required.
"""

from __future__ import annotations

import argparse
from array import array
from collections import deque
from itertools import product
import json
from pathlib import Path
from time import perf_counter


class FiniteAbelianGroup:
    def __init__(self, moduli: tuple[int, ...]):
        self.moduli = moduli
        self.points = list(product(*(range(n) for n in moduli)))
        self.n = len(self.points)
        self.full = (1 << self.n) - 1
        self.index = {p: i for i, p in enumerate(self.points)}
        self.add = [
            [self.index[tuple((a + b) % n for a, b, n in zip(x, y, moduli))]
             for y in self.points]
            for x in self.points
        ]
        self.neg = [
            self.index[tuple((-a) % n for a, n in zip(x, moduli))]
            for x in self.points
        ]
        # Flattened translation table: translates[mask*n+d] is mask+d.
        # Every table entry is constructed by adding one bit to a smaller mask.
        self.translates = array('I', [0]) * ((1 << self.n) * self.n)
        self.neg_masks = array('I', [0]) * (1 << self.n)
        for mask in range(1, 1 << self.n):
            bit = mask & -mask
            i = bit.bit_length() - 1
            prev = mask ^ bit
            base = mask * self.n
            prev_base = prev * self.n
            self.neg_masks[mask] = self.neg_masks[prev] | (1 << self.neg[i])
            for d in range(self.n):
                self.translates[base + d] = (
                    self.translates[prev_base + d] | (1 << self.add[i][d]))
        self.subgroups = self._subgroups()
        self.all_cosets = sorted({
            c for h in self.subgroups for c in self.cosets(h)})

    @property
    def name(self):
        return ' x '.join(f'C{n}' for n in self.moduli)

    def shift(self, mask, d):
        return self.translates[mask * self.n + d]

    def convolution(self, a, b):
        base = self.neg_masks[b] * self.n
        return [(a & self.translates[base + x]).bit_count()
                for x in range(self.n)]

    def correlation(self, a, b=None):
        if b is None:
            b = a
        base = b * self.n
        return [(a & self.translates[base + x]).bit_count()
                for x in range(self.n)]

    def is_subgroup(self, mask):
        return mask in self.subgroups

    def cosets(self, h):
        remaining = self.full
        out = []
        while remaining:
            d = (remaining & -remaining).bit_length() - 1
            c = self.shift(h, d)
            out.append(c)
            remaining &= ~c
        return out

    def _subgroups(self):
        known = {1}
        queue = deque([1])
        while queue:
            h = queue.popleft()
            for g in range(self.n):
                if h >> g & 1:
                    continue
                k = h
                x = g
                while not (h >> x & 1):
                    k |= self.shift(h, x)
                    x = self.add[x][g]
                if k not in known:
                    known.add(k)
                    queue.append(k)
        return known


def require(condition, message, **data):
    if not condition:
        raise AssertionError(f'{message}: {data}')


def punctured_coset_data(group, a, r):
    """Return (stabilizer, enclosing subgroup, enclosing coset), or None."""
    m = a.bit_count()
    stabilizer = sum(1 << d for d, v in enumerate(r) if v == m)
    l = stabilizer.bit_count()
    differences = sum(1 << d for d, v in enumerate(r) if v)
    if not group.is_subgroup(differences):
        return stabilizer, None, None
    if differences.bit_count() != m + l:
        return stabilizer, None, None
    first = (a & -a).bit_length() - 1
    enclosing = group.shift(differences, first)
    if a & ~enclosing:
        return stabilizer, None, None
    hole = enclosing ^ a
    if hole not in group.cosets(stabilizer):
        return stabilizer, None, None
    return stabilizer, differences, enclosing


def verify_sets(group):
    started = perf_counter()
    counts = dict(sets=0, pointwise_cases=0, remainder_identities=0,
                  multilevel_cases=0, high_energy_sets=0,
                  pointwise_equalities=0, envelope_equalities=0)
    for a in range(1, 1 << group.n):
        counts['sets'] += 1
        m = a.bit_count()
        m3 = m ** 3
        r = group.correlation(a)
        z = group.convolution(a, a)
        energy = sum(v * v for v in r)
        require(energy == sum(v * v for v in z), 'sum/difference energy',
                group=group.name, a=a)
        defect = m3 - energy
        stabilizer, enclosing_group, enclosing = punctured_coset_data(group, a, r)
        l = stabilizer.bit_count()
        require(group.is_subgroup(stabilizer), 'stabilizer subgroup', a=a)
        k = m // l

        for d, t in enumerate(r):
            counts['pointwise_cases'] += 1
            gap = defect - m * t * (m - t)
            require(gap >= 0, 'pointwise bound', group=group.name, a=a, d=d)
            equal = gap == 0
            if defect == 0:
                expected = True
            elif k == 2:
                expected = t == l
            else:
                expected = (enclosing_group is not None and k >= 3
                            and bool(enclosing_group >> d & 1)
                            and not bool(stabilizer >> d & 1))
            require(equal == expected, 'complete pointwise equality classification',
                    group=group.name, a=a, d=d, r=r)
            counts['pointwise_equalities'] += equal

            b = group.shift(a, d)
            c, u = a & b, a | b
            p, q = a & ~b, b & ~a
            w = group.convolution(c, u)
            v = group.convolution(p, q)
            s = group.convolution(a, b)
            require(all(x + y == z0 for x, y, z0 in zip(w, v, s)),
                    'union/intersection convolution identity', a=a, d=d)
            require(all(0 <= x <= t for x in w)
                    and all(0 <= x <= m - t for x in v), 'pointwise caps', a=a)
            rhs = ((m - t) ** 3 - sum(x * x for x in v)
                   + sum((t - x) * (x + 2 * y) for x, y in zip(w, v)))
            require(gap == rhs, 'exact positive remainder', a=a, d=d)
            counts['remainder_identities'] += 1
            require(sum(min(x, t) for x in z) >= t * (2 * m - t),
                    'sum truncation at attained difference multiplicity', a=a, d=d)

        levels = sorted(set(r) | {0, m})
        cubes = sum((y - x) ** 3 for x, y in zip(levels, levels[1:]))
        require(3 * defect >= m3 - cubes, 'multilevel bound', a=a, r=r)
        counts['multilevel_cases'] += 1

        if 4 * defect > m3:
            continue
        counts['high_energy_sets'] += 1
        hmask = sum(1 << d for d, v in enumerate(r) if 2 * v > m)
        require(group.is_subgroup(hmask), 'high-overlap subgroup through 1/4',
                group=group.name, a=a, r=r)
        h = hmask.bit_count()
        cosets = group.cosets(hmask)
        occupancies = [(a & c).bit_count() for c in cosets]
        amax = max(occupancies)
        canonical = [c for c, occ in zip(cosets, occupancies) if occ == amax]
        distance = m + h - 2 * amax
        # On [0,1/2], delta<=tau iff delta(1-delta)<=epsilon.
        require(2 * distance <= m and m * distance * (m - distance) <= defect,
                'global sharp coset envelope', group=group.name, a=a, r=r)
        envelope_equal = defect == m * distance * (m - distance)
        counts['envelope_equalities'] += envelope_equal
        if defect == 0:
            expected = True
        elif 4 * defect < m3:
            expected = enclosing_group is not None and k >= 3
        else:
            expected = k == 2
        require(envelope_equal == expected, 'complete global envelope equality',
                group=group.name, a=a, r=r, distance=distance)
        require((len(canonical) > 1) == (4 * defect == m3 and k == 2),
                'canonical coset uniqueness characterization', group=group.name, a=a)

        all_distances = [(a ^ c).bit_count() for c in group.all_cosets]
        best = min(all_distances)
        nearest = {c for c, dist in zip(group.all_cosets, all_distances) if dist == best}
        if 9 * defect < 2 * m3:
            require(nearest == set(canonical), 'strict 2/9 global uniqueness',
                    group=group.name, a=a)
        if 4 * defect == m3 and k == 2:
            expected_nearest = set(canonical)
            if enclosing is not None:
                expected_nearest.add(enclosing)
            require(nearest == expected_nearest and best == m // 2,
                    'all endpoint closest cosets', group=group.name, a=a)
        if enclosing is not None and k == 3:
            expected_nearest = {enclosing}
            expected_nearest.update(c for c in group.all_cosets
                                    if c.bit_count() == 2 * l and c & ~a == 0)
            require(nearest == expected_nearest and best == l,
                    'all index-four puncture closest cosets', group=group.name, a=a)
    counts['seconds'] = round(perf_counter() - started, 3)
    return counts


def verify_mixed(group):
    started = perf_counter()
    pairs = 0
    pointwise_cases = 0
    for original_a in range(1, 1 << group.n):
        for original_b in range(1, 1 << group.n):
            a, b = original_a, original_b
            na, nb = a.bit_count(), b.bit_count()
            if na < nb:
                a, b, na, nb = b, a, nb, na
            s = group.convolution(a, b)
            energy = sum(x * x for x in s)
            defect = na * nb ** 2 - energy
            for t in group.correlation(a, b):
                require(defect >= nb * t * (nb - t), 'mixed overlap bound',
                        group=group.name, a=a, b=b, t=t)
                pointwise_cases += 1
            t = (a & b).bit_count()
            c, u, p, q = a & b, a | b, a & ~b, b & ~a
            w, v = group.convolution(c, u), group.convolution(p, q)
            require(all(x + y == z for x, y, z in zip(w, v, s)),
                    'mixed union/intersection identity', a=a, b=b)
            rhs = ((na - t) * (nb - t) ** 2 - sum(x * x for x in v)
                   + sum((t - x) * (x + 2 * y) for x, y in zip(w, v)))
            require(defect - nb * t * (nb - t) == rhs >= 0,
                    'mixed exact positive remainder', group=group.name, a=a, b=b)
            pairs += 1
    return dict(ordered_pairs=pairs, translated_pointwise_cases=pointwise_cases,
                seconds=round(perf_counter() - started, 3))


def verify_sharpness():
    checked = []
    # Direct evaluation in C_h x C5 without exponential translation tables.
    for h in (1, 2, 4, 8, 16, 32, 64):
        a = {(x, y) for x in range(h) for y in (0, 1)} | {(0, 2)}
        r = {}
        for x in a:
            for y in a:
                d = ((x[0] - y[0]) % h, (x[1] - y[1]) % 5)
                r[d] = r.get(d, 0) + 1
        m = 2 * h + 1
        energy = sum(x * x for x in r.values())
        require(energy == 6 * h ** 3 + 4 * h ** 2 + 8 * h + 1,
                'finite sharpness energy', h=h)
        require(2 * r[(0, 1)] > m and 2 * r[(0, 2)] <= m,
                'finite sharpness closure failure', h=h)
        require(4 * (m ** 3 - energy) - m ** 3 == 20 * h ** 2 - 14 * h - 1 > 0,
                'finite sharpness exact excess', h=h)
        best = 10 * h
        ell = 1
        while ell <= h:
            step = h // ell
            for offset in range(step):
                first_factor = {(offset + i * step) % h for i in range(ell)}
                for level in range(5):
                    c = {(x, level) for x in first_factor}
                    best = min(best, len(a ^ c))
                c = {(x, level) for x in first_factor for level in range(5)}
                best = min(best, len(a ^ c))
            ell *= 2
        require(best == h + 1, 'finite sharpness nearest coset', h=h)
        checked.append(dict(h=h, m=m, energy=energy, nearest_distance=best))
    return checked


def raw_convolution(group, a, b):
    result = [0] * group.n
    for i, x in enumerate(a):
        if not x:
            continue
        for j, y in enumerate(b):
            if y:
                result[group.add[i][j]] += x * y
    return result


def verify_rational_weights():
    """Use integer numerators for weights in {0,1/2,1}; no floating point."""
    started = perf_counter()
    report = dict(arithmetic='exact integer numerators; common weight denominator 2',
                  groups={})
    for moduli in [(n,) for n in range(1, 7)] + [(2, 2), (2, 2, 2)]:
        group = FiniteAbelianGroup(moduli)
        functions = [f for f in product(range(3), repeat=group.n) if any(f)]
        counts = dict(functions=0, shifted_remainder_identities=0,
                      multilevel_cases=0, high_energy_closure_cases=0,
                      mixed_ordered_pairs=0)
        for f in functions:
            counts['functions'] += 1
            mass = sum(f)
            s0 = raw_convolution(group, f, f)
            # Actual mass=mass/2, actual energy=energy_integer/16.
            energy_integer = sum(x * x for x in s0)
            deficit = 2 * mass ** 3 - energy_integer
            overlaps = []
            for d in range(group.n):
                g = [f[group.add[x][group.neg[d]]] for x in range(group.n)]
                c = [min(x, y) for x, y in zip(f, g)]
                u = [max(x, y) for x, y in zip(f, g)]
                p = [x - z for x, z in zip(f, c)]
                q = [y - z for y, z in zip(g, c)]
                t = sum(c)
                k = mass - t
                overlaps.append(t)
                w = raw_convolution(group, c, u)
                v = raw_convolution(group, p, q)
                s = raw_convolution(group, f, g)
                require(all(x + y == z for x, y, z in zip(w, v, s)),
                        'weighted convolution identity', group=group.name, f=f, d=d)
                gap = deficit - 2 * mass * t * k
                rhs = (2 * k ** 3 - sum(x * x for x in v)
                       + sum((2 * t - x) * (x + 2 * y) for x, y in zip(w, v)))
                require(gap == rhs >= 0, 'weighted positive remainder',
                        group=group.name, f=f, d=d)
                require(sum(min(x, 2 * t) for x in s0) >= t * (2 * mass - t),
                        'weighted sum truncation', group=group.name, f=f, d=d)
                counts['shifted_remainder_identities'] += 1
            levels = sorted(set(overlaps) | {0, mass})
            cubes = sum((y - x) ** 3 for x, y in zip(levels, levels[1:]))
            require(3 * deficit >= 2 * (mass ** 3 - cubes),
                    'weighted multilevel inequality', group=group.name, f=f)
            counts['multilevel_cases'] += 1
            if 2 * deficit <= mass ** 3:
                h = sum(1 << d for d, t in enumerate(overlaps) if 2 * t > mass)
                require(group.is_subgroup(h), 'weighted high-overlap subgroup',
                        group=group.name, f=f)
                counts['high_energy_closure_cases'] += 1
        # Every ordered pair, hence every shifted mixed pair, for orders <=4.
        if group.n <= 4:
            for original_f in functions:
                for original_g in functions:
                    f, g = original_f, original_g
                    a, b = sum(f), sum(g)
                    if a < b:
                        f, g, a, b = g, f, b, a
                    c = [min(x, y) for x, y in zip(f, g)]
                    u = [max(x, y) for x, y in zip(f, g)]
                    p = [x - z for x, z in zip(f, c)]
                    q = [y - z for y, z in zip(g, c)]
                    t = sum(c)
                    w = raw_convolution(group, c, u)
                    v = raw_convolution(group, p, q)
                    s = raw_convolution(group, f, g)
                    gap = (2 * a * b ** 2 - sum(x * x for x in s)
                           - 2 * b * t * (b - t))
                    rhs = (2 * (a - t) * (b - t) ** 2 - sum(x * x for x in v)
                           + sum((2 * t - x) * (x + 2 * y)
                                 for x, y in zip(w, v)))
                    require(gap == rhs >= 0, 'weighted mixed positive remainder',
                            group=group.name, f=f, g=g)
                    counts['mixed_ordered_pairs'] += 1
        report['groups'][group.name] = counts
        print(f"PASS rational weights {group.name}: {counts}", flush=True)
    report['totals'] = {
        key: sum(result[key] for result in report['groups'].values())
        for key in ('functions', 'shifted_remainder_identities', 'multilevel_cases',
                    'high_energy_closure_cases', 'mixed_ordered_pairs')}
    report['total_seconds'] = round(perf_counter() - started, 3)
    return report


def main():
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--max-cyclic', type=int, default=16,
                        help='maximum exhaustively enumerated cyclic order (2..16)')
    parser.add_argument('--output', type=Path, default=None,
                        help='JSON destination (default: package data directory)')
    parser.add_argument('--weights-only', action='store_true',
                        help='run the separate rational-weight suite instead')
    args = parser.parse_args()
    if args.output is None:
        filename = ('weighted_energy_checks.json' if args.weights_only
                    else 'energy_checks.json')
        args.output = Path(__file__).resolve().parents[1] / 'data' / filename
    args.output.parent.mkdir(parents=True, exist_ok=True)
    if args.weights_only:
        report = verify_rational_weights()
        args.output.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
        print(json.dumps(report['totals'], indent=2), flush=True)
        print(f"All rational-weight checks passed in {report['total_seconds']:.3f} s.",
              flush=True)
        return
    if not 2 <= args.max_cyclic <= 16:
        parser.error('--max-cyclic must be between 2 and 16')
    started = perf_counter()
    cyclic = [(n,) for n in range(2, args.max_cyclic + 1)]
    products = [(2, 2), (2, 2, 2), (3, 3), (4, 2),
                (2, 2, 2, 2), (4, 4), (8, 2), (4, 2, 2)]
    report = dict(arithmetic='exact integers only', sets={}, mixed={})
    for moduli in cyclic + products:
        group = FiniteAbelianGroup(moduli)
        result = verify_sets(group)
        report['sets'][group.name] = result
        print(f"PASS sets {group.name}: {result['sets']} sets, "
              f"{result['seconds']:.3f} s", flush=True)
        if group.n <= 9:
            result = verify_mixed(group)
            report['mixed'][group.name] = result
            print(f"PASS mixed {group.name}: {result['ordered_pairs']} pairs, "
                  f"{result['seconds']:.3f} s", flush=True)
    report['sharpness'] = verify_sharpness()
    report['totals'] = {
        key: sum(result[key] for result in report['sets'].values())
        for key in ('sets', 'pointwise_cases', 'remainder_identities',
                    'multilevel_cases', 'high_energy_sets', 'pointwise_equalities',
                    'envelope_equalities')}
    report['totals']['mixed_ordered_pairs'] = sum(
        result['ordered_pairs'] for result in report['mixed'].values())
    report['totals']['mixed_translated_pointwise_cases'] = sum(
        result['translated_pointwise_cases'] for result in report['mixed'].values())
    report['total_seconds'] = round(perf_counter() - started, 3)
    args.output.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(report['totals'], indent=2), flush=True)
    print(f"All checks passed in {report['total_seconds']:.3f} s.", flush=True)


if __name__ == '__main__':
    main()
