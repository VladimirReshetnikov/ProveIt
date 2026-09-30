#!/usr/bin/env python3
"""Exact finite checks for Mixed-Volume Tomography of Surreal Polytopes.

Arithmetic is in Q(t), ordered at positive infinitesimal t.  These checks
exercise finite examples; they are not a formal proof of the manuscript.
Requires Python >=3.10 and SymPy >=1.12.
"""
from __future__ import annotations
import itertools as it
import json
import random
from collections import Counter
from functools import cmp_to_key
from pathlib import Path
from typing import Sequence
from sympy.polys.fields import field
from sympy.polys.domains import QQ

F, t = field('t', QQ)
INF = float('inf')
SEED = 2026093017
rng = random.Random(SEED)
checks = Counter()


def check(condition: bool, group: str, detail: str = '') -> None:
    if not condition:
        raise AssertionError(f'{group}: {detail}')
    checks[group] += 1


def val(x):
    x = F(x)
    if not x:
        return INF
    return min(m[0] for m in x.numer.monoms()) - min(m[0] for m in x.denom.monoms())


def sign(x) -> int:
    x = F(x)
    if not x:
        return 0
    nc = min(x.numer.terms(), key=lambda p: p[0])[1]
    dc = min(x.denom.terms(), key=lambda p: p[0])[1]
    return 1 if nc * dc > 0 else -1


def det(a):
    """Leibniz formula, independent of the pivot algorithm below."""
    n = len(a)
    if n == 0:
        return F.one
    total = F.zero
    for p in it.permutations(range(n)):
        term = F.one
        for i in range(n):
            term *= a[i][p[i]]
        inv = sum(p[i] > p[j] for i in range(n) for j in range(i + 1, n))
        total += (-term if inv % 2 else term)
    return total


def columns(a):
    return [tuple(a[i][j] for i in range(len(a))) for j in range(len(a[0]))]


def matrix(cols):
    return [[F(cols[j][i]) for j in range(len(cols))] for i in range(len(cols[0]))]


def mmul(a, b):
    return [[sum((a[i][k] * b[k][j] for k in range(len(b))), F.zero)
             for j in range(len(b[0]))] for i in range(len(a))]


def inverse(a):
    n = len(a)
    aug = [[F(x) for x in row] + [F(int(i == j)) for j in range(n)]
           for i, row in enumerate(a)]
    for k in range(n):
        pivot = next((i for i in range(k, n) if aug[i][k]), None)
        if pivot is None:
            raise ValueError('Singular matrix')
        aug[k], aug[pivot] = aug[pivot], aug[k]
        p = aug[k][k]
        aug[k] = [x / p for x in aug[k]]
        for i in range(n):
            if i != k:
                q = aug[i][k]
                aug[i] = [x - q * y for x, y in zip(aug[i], aug[k])]
    return [row[n:] for row in aug]


def delta(a, k):
    if k == 0:
        return 0
    return min(val(det([[a[i][j] for j in js] for i in rs]))
               for rs in it.combinations(range(len(a)), k)
               for js in it.combinations(range(len(a[0])), k))


def profile(a):
    return [delta(a, k) for k in range(len(a) + 1)]


def pivot_spectrum(a):
    a = [[F(x) for x in row] for row in a]
    d, n = len(a), len(a[0])
    out = []
    for k in range(min(d, n)):
        v, i, j = min((val(a[i][j]), i, j)
                      for i in range(k, d) for j in range(k, n))
        if v == INF:
            break
        a[k], a[i] = a[i], a[k]
        for row in a:
            row[k], row[j] = row[j], row[k]
        p = a[k][k]
        out.append(v)
        for i in range(k + 1, d):
            q = a[i][k] / p
            check(val(q) >= 0, 'integral_pivot_multipliers')
            a[i] = [x - q * y for x, y in zip(a[i], a[k])]
        # Clear the rest of row k by integral column operations.
        for j in range(k + 1, n):
            q = a[k][j] / p
            check(val(q) >= 0, 'integral_pivot_multipliers')
            for i in range(d):
                a[i][j] -= q * a[i][k]
    return out


def module_basis(a):
    d = len(a)
    choices = [(val(det([[a[i][j] for j in js] for i in range(d)])), js)
               for js in it.combinations(range(len(a[0])), d)]
    v, js = min(choices)
    if v == INF:
        raise ValueError('Module must have full rank')
    return [[a[i][j] for j in js] for i in range(d)]


def integral(a):
    return all(val(x) >= 0 for row in a for x in row)


def cross(a, b):
    return a[0] * b[1] - a[1] * b[0]


def minus(a, b):
    return tuple(x - y for x, y in zip(a, b))


def cmp_points(a, b):
    return sign(a[0] - b[0]) or sign(a[1] - b[1])


def hull(points):
    points = sorted(set(points), key=cmp_to_key(cmp_points))
    if len(points) <= 1:
        return points
    lower, upper = [], []
    for p in points:
        while len(lower) >= 2 and sign(cross(minus(lower[-1], lower[-2]), minus(p, lower[-1]))) <= 0:
            lower.pop()
        lower.append(p)
    for p in reversed(points):
        while len(upper) >= 2 and sign(cross(minus(upper[-1], upper[-2]), minus(p, upper[-1]))) <= 0:
            upper.pop()
        upper.append(p)
    return lower[:-1] + upper[:-1]


def area(points):
    h = hull(points)
    if len(h) < 3:
        return F.zero
    s = sum((cross(h[i], h[(i + 1) % len(h)]) for i in range(len(h))), F.zero) / 2
    check(sign(s) >= 0, 'nonnegative_hull_area')
    return s


def mixed_area(p, q):
    sums = [tuple(a + b for a, b in zip(x, y)) for x in p for y in q]
    return (area(sums) - area(p) - area(q)) / 2


def displacements(p):
    return [minus(x, p[0]) for x in p[1:]]


def colorful(groups):
    d = len(groups)
    if any(not g for g in groups):
        return INF
    return min(val(det(matrix(ws))) for ws in it.product(*groups))


def poly():
    return sum((rng.randint(-2, 2) * t**rng.randint(0, 4) for _ in range(2)), F.zero)


def random_matrix(d, n):
    return [[poly() for _ in range(n)] for _ in range(d)]


def rectangle(a, b):
    z = (F.zero, F.zero)
    return [z, a, b, tuple(x + y for x, y in zip(a, b))]


def main():
    examples = {}
    # Independent hull computation versus the colorful-determinant theorem.
    for _ in range(100):
        p = [(poly(), poly()) for _ in range(rng.randint(3, 6))]
        q = [(poly(), poly()) for _ in range(rng.randint(3, 6))]
        mv = mixed_area(p, q)
        check(sign(mv) >= 0, 'mixed_area_nonnegative')
        check(val(mv) == colorful([displacements(p), displacements(q)]),
              'colorful_formula_independent_hulls')
    # All minors versus independent valuation-pivot elimination.
    for d in range(2, 5):
        for _ in range(30):
            a = random_matrix(d, d + 1)
            ds = profile(a)
            ps = pivot_spectrum(a)
            check(ps == sorted(ps), 'ordered_pivot_spectrum')
            check([sum(ps[:k]) for k in range(len(ps) + 1)] == ds[:len(ps) + 1],
                  'minor_profile_equals_pivot_profile')
            if len(ps) == d:
                b = module_basis(a)
                check(integral(mmul(inverse(b), a)), 'minimum_determinant_basis')
                dual = list(map(list, zip(*inverse(b))))
                pd = pivot_spectrum(dual)
                check(pd == [-x for x in reversed(ps)], 'polar_dual_spectrum')
                # Redundant integral generators cannot alter the profile.
                cs = columns(a)
                extra = tuple(cs[0][i] + t**2 * cs[-1][i] for i in range(d))
                check(profile(matrix(cs + [extra])) == ds, 'redundant_generator_invariance')
    # The adaptive tomography criterion against direct double containment.
    for _ in range(50):
        a, c = random_matrix(2, 3), random_matrix(2, 3)
        if delta(a, 2) == INF or delta(c, 2) == INF:
            continue
        b, e = module_basis(a), module_basis(c)
        coords = mmul(inverse(b), c)
        tau = val(det(b))
        probe = [min(val(x) for x in row) for row in coords]
        criterion = min(probe) >= 0 and delta(c, 2) == tau
        direct = integral(mmul(inverse(b), e)) and integral(mmul(inverse(e), b))
        check(criterion == direct, 'adaptive_tomography')
    # Exact rank-two range and its constructive realization.
    for p in range(3):
        for q in range(p, 5):
            for r in range(3):
                for s in range(r, 5):
                    gap = min(q - p, s - r)
                    for beta in range(gap + 2):
                        x = [(t**p, F.zero), (F.zero, t**q)]
                        y = [(t**r, t**(r + beta)), (F.zero, t**s)]
                        got = colorful([x, y])
                        expected = p + r + min(beta, gap)
                        check(got == expected, 'rank_two_interaction_range')
    # Perturbations above selected invariant scales preserve initial profiles.
    for _ in range(45):
        alphas = sorted(rng.randint(-2, 6) for _ in range(3))
        a = [[t**alphas[i] if i == j else F.zero for j in range(3)] for i in range(3)]
        rho = rng.randint(-1, 8)
        e = [[rng.randint(-2, 2) * t**rho for _ in range(3)] for _ in range(3)]
        ap = [[a[i][j] + e[i][j] for j in range(3)] for i in range(3)]
        for k in range(1, 4):
            if rho > alphas[k - 1]:
                check(delta(ap, k) == sum(alphas[:k]), 'partial_profile_stability')
        if rho > alphas[-1]:
            check(integral(mmul(inverse(a), ap)) and integral(mmul(inverse(ap), a)),
                  'full_module_stability')
    a = [[F.one, F.zero], [F.zero, t**3]]
    ap = [[F.one, F.zero], [F.zero, t**7]]
    check(val(ap[1][1] - a[1][1]) == 3 and delta(a, 2) != delta(ap, 2),
          'sharp_boundary_counterexample')
    # Explicit hidden-shear formula, checked with hulls rather than determinants.
    p = rectangle((F.one, F.zero), (F.zero, t**8))
    q = rectangle((F.one, t**3), (F.zero, t**8))
    mv = mixed_area(p, q)
    check(mv == t**8 + t**3 / 2, 'hidden_shear_exact_mixed_area')
    examples['hidden_shear'] = {'mixed_area': str(mv), 'valuation': val(mv),
                                'individual_spectrum': [0, 8]}
    # Any finite preset family of planar test bodies can be defeated.
    tests = [[(poly(), poly()) for _ in range(4)] for _ in range(18)]
    zs = [z for body in tests for z in displacements(body) if any(z)]
    c = next(c for c in range(len(zs) + 2)
             if all(val(cross((F.one, F(c)), z)) == min(map(val, z)) for z in zs))
    p0 = rectangle((F.one, F(c)), (F.zero, t**8))
    ph = rectangle((F.one, F(c) + t**3), (F.zero, t**8))
    for test in tests:
        check(val(mixed_area(p0, test)) == val(mixed_area(ph, test)),
              'fixed_probe_impossibility_examples')
    bp = matrix([(F.one, F(c)), (F.zero, t**8)])
    bq = matrix([(F.one, F(c) + t**3), (F.zero, t**8)])
    check(val(area(p0)) == val(area(ph)) == 8, 'fixed_probe_equal_area')
    check(profile(bp) == profile(bq) == [0, 0, 8], 'fixed_probe_equal_profiles')
    check(not integral(mmul(inverse(bp), bq)), 'fixed_probe_different_modules')
    examples['fixed_probe_family'] = {'number_of_test_bodies': len(tests), 'chosen_slope': c,
                                      'strip_thickness': 't^8', 'hidden_shear': 't^3'}
    # Independent projection-volume identity in dimension two.
    cube = rectangle((F.one, F.zero), (F.zero, F.one))
    for _ in range(20):
        pp = [(poly(), poly()) for _ in range(5)]
        xs = sorted([x for x, y in pp], key=cmp_to_key(lambda a, b: sign(a - b)))
        ys = sorted([y for x, y in pp], key=cmp_to_key(lambda a, b: sign(a - b)))
        check(2 * mixed_area(pp, cube) == xs[-1] - xs[0] + ys[-1] - ys[0],
              'cube_projection_identity')
    report = {'status': 'PASS', 'seed': SEED, 'arithmetic': 'exact Q(t), t positive infinitesimal',
              'total_assertions': sum(checks.values()), 'groups': dict(sorted(checks.items())),
              'examples': examples,
              'scope': 'Finite exact checks only; not Lean verification or proof of arbitrary-rank statements.'}
    out = Path(__file__).resolve().parents[1] / 'data' / 'verification.json'
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
