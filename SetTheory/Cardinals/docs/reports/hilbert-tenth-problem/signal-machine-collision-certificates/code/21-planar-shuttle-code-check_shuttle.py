#!/usr/bin/env python3
"""Deterministic, optimized-safe proof regressions (standard library only).

All checks raise explicitly; Python -O does not delete any test. This suite
does not claim to exhaust the 2**169 local windows or all configurations.
"""
from collections import Counter
from itertools import combinations, product
from pathlib import Path
from random import Random
import argparse
import json
import component_rule as direct
import exact_formulas as formula
import local_rule as local


def require(condition, detail):
    if not condition:
        raise RuntimeError(detail)


def compare(support, wide=False):
    a = direct.step(support)
    b = local.step(support, search_radius=6 if wide else 1)
    require(a == b, ('local/direct mismatch', support, a, b))
    require(len(a) == len(support), ('mass mismatch', support, a))


def run():
    counts = Counter()
    rng = Random(202610030631)
    require(local.evaluate(0) == 0, 'vacuum is not quiescent')
    require(direct.step(set()) == set(), 'empty direct step')
    require(local.step(set()) == set(), 'empty local step')
    # Every local cylinder fits [-6,6]^2 and has disjoint prescribed bits.
    for p, q in local.BIRTHS + local.REMOVALS:
        require(p > 0 and q > 0 and p & q == 0, 'invalid cylinder')
        require((p | q).bit_length() <= 169, 'radius overflow')
        counts['cylinder_checks'] += 1

    # Exhaust all supports in a genuinely planar 4-by-3 rectangle.
    cells = tuple(product(range(4), range(3)))
    for mask in range(1 << len(cells)):
        c = {p for i, p in enumerate(cells) if mask >> i & 1}
        compare(c)
        counts['exhaustive_planar_supports'] += 1

    # Exhaust all supports of a horizontal 13-site interval, spanning radius 6.
    for mask in range(1 << 13):
        c = {(i, 0) for i in range(13) if mask >> i & 1}
        compare(c)
        counts['exhaustive_line_supports'] += 1

    # Independent whole-window checks, including arbitrary exterior data.
    for _ in range(2500):
        density = rng.choice((0.015, 0.04, 0.1, 0.3, 0.7))
        c = {(x, y) for x in range(-9, 10) for y in range(-9, 10)
             if rng.random() < density}
        mask = local.neighborhood(c, (0, 0))
        require(local.evaluate(mask) == int((0, 0) in direct.step(c)),
                ('random neighborhood mismatch', c))
        clipped = {p for p in c if max(map(abs, p)) <= 6}
        require(int((0, 0) in direct.step(c)) ==
                int((0, 0) in direct.step(clipped)), 'radius-six locality failed')
        counts['random_radius_and_exterior_checks'] += 1

    # Every one-site alteration around every primitive active component.
    for shape in direct.RULES:
        base = set(shape)
        for p in product(range(-5, 10), range(-4, 5)):
            compare(base ^ {p})
            counts['single_site_template_perturbations'] += 1
        for offset in ((0, 0), (10**12, -10**12), (-10**15, 10**15)):
            x, y = offset
            translated = {(a+x, b+y) for a, b in base}
            expected = {(a+x, b+y) for a, b in direct.step(base)}
            require(direct.step(translated) == expected, 'translation mismatch')
            require(local.step(translated) == expected, 'local translation mismatch')
            counts['large_translation_checks'] += 1

    # Interacting active and malformed shapes; unions may merge and freeze.
    shapes = list(map(set, direct.RULES)) + [
        {(0, 0)}, {(0, 0), (0, 1)}, {(0, 0), (1, 1), (2, 2)},
        {(0, 0), (1, 0), (2, 0), (3, 0)},
    ]
    for a, b in product(shapes, repeat=2):
        for dx, dy in product(range(-5, 6), range(-3, 4)):
            c = a | {(x+dx, y+dy) for x, y in b}
            compare(c)
            counts['two_template_union_checks'] += 1

    # Search the entire radius-six possible output area to detect ghost births.
    for _ in range(160):
        c = {(rng.randrange(-10, 11), rng.randrange(-5, 6))
             for _ in range(rng.randrange(1, 18))}
        compare(c, wide=True)
        require(local.drift_step(c) == direct.drift_step(c),
                'drifted independent local mismatch')
        counts['full_radius_output_searches'] += 1

    # Explicit unit-distance matching for every primitive rule, and halo bounds.
    matchings = (
        (((0, 0), (1, 0)), ((1, 0), (2, 0))),
        (((0, 0), (-1, 0)), ((2, 0), (1, 0))),
        (((0, 0), (-1, 0)), ((1, 0), (1, 0)), ((3, 0), (4, 1))),
        (((0, 0), (0, 1)), ((2, 0), (3, 1)), ((4, 0), (4, 1))),
    )
    for (old, new), matching in zip(direct.RULES.items(), matchings):
        require({a for a, _ in matching} == set(old), 'matching source mismatch')
        require({b for _, b in matching} == set(new), 'matching target mismatch')
        for a, b in matching:
            require(max(abs(a[i]-b[i]) for i in (0, 1)) <= 1,
                    'matching displacement exceeds one')
        for p in set(old) ^ set(new):
            for q in old:
                require(max(abs(p[i]-q[i]) for i in (0, 1)) <= 4,
                        'halo locality estimate exceeded')
        counts['primitive_matching_and_radius_checks'] += 1

    # Every phase boundary, first arrival, and whole row across many rounds.
    for k in range(7, 31):
        c = direct.initial(k)
        first = {}
        t = 0
        for n in range(45):
            d = k+n
            require(t == formula.section_time(k, n), 'section clock mismatch')
            for j in range(2*d-10):
                require(c == direct.phase_support(k, n, j),
                        ('phase mismatch', k, n, j, c))
                for p in c:
                    first.setdefault(p, t)
                if n < 2:
                    require(local.step(c) == direct.step(c), 'local orbit mismatch')
                    counts['independent_local_orbit_steps'] += 1
                c = direct.step(c)
                require(len(c) == 4, 'orbit mass mismatch')
                t += 1
                counts['direct_orbit_phase_steps'] += 1
            require(c == {(0, n+1), (3, n+1), (4, n+1), (d+1, n+1)},
                    'next section mismatch')
            counts['completed_cycle_checks'] += 1
        # First 45 rows have been fully swept, including their last x=2 site.
        for n in range(45):
            actual = {x for (x, y) in first if y == n}
            expected = {0, k+n} | set(range(2, k+n-1))
            require(actual == expected, ('row-set mismatch', k, n, actual))
            for x in range(-1, k+n+2):
                require(first.get((x, n)) == formula.first_arrival(k, x, n),
                        ('first arrival mismatch', k, x, n))
                counts['first_arrival_checks'] += 1
        for radius in range(45):
            actual = sum(max(abs(x), abs(y)) <= radius for x, y in first)
            require(actual == formula.centered_count(k, radius),
                    ('centered count mismatch', k, radius, actual))
            counts['centered_count_checks'] += 1

    # Original-frame trace: check all four sites are new at every time.
    for k in range(7, 41):
        c = direct.initial(k)
        seen, shells = set(), Counter()
        for t in range(1601):
            require(not (seen & c), ('drift cross-time collision', k, t, seen & c))
            seen.update(c)
            shells.update(max(abs(x), abs(y)) for x, y in c)
            c = direct.drift_step(c)
            counts['drift_disjoint_trace_steps'] += 1
        total = 0
        for radius in range(1601):
            total += shells[radius]
            if radius >= k+1:
                require(total == formula.drift_count(k, radius),
                        ('drift count mismatch', k, radius, total))
                counts['drift_count_checks'] += 1

    # Floor-square-root formulas against direct enumeration, including edges.
    for linear in range(0, 17):
        for constant in (-5, -1, 0, 2, 12):
            for first in (0, 1, 3):
                for bound in range(0, 101):
                    expected = sum(n*n+linear*n+constant <= bound
                                   for n in range(first, 30))
                    require(formula.quadratic_count(bound, linear, constant, first)
                            == expected, 'quadratic floor count mismatch')
                    counts['quadratic_floor_checks'] += 1

    return {
        'status': 'PASS', 'alphabet': [0, 1], 'numerical_mass': 4,
        'spatial_dimension': 2, 'radius_upper_bound': 6,
        'drifted_radius_upper_bound': 6,
        'checks': dict(sorted(counts.items())),
        'optimized_safe': 'Every check uses explicit exceptions, never assert.',
        'independence': ('Local evaluator imports no component simulator or '
                         'shared rewrite table; it uses independent cylinders.'),
        'limits': ('Finite tests supplement the all-configuration proof. They '
                   'do not enumerate all 2**169 local windows. No reversibility '
                   'or radius minimality is asserted.'),
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path)
    parser.add_argument('--certificate', type=Path)
    args = parser.parse_args()
    result = run()
    text = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.output:
        args.output.write_text(text)
    if args.certificate:
        args.certificate.write_text(json.dumps(local.certificate(), indent=2,
                                               sort_keys=True) + '\n')
    print(text, end='')
