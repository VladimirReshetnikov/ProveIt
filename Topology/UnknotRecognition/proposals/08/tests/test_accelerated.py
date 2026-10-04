"""Regression and independent-model tests for the acceleration layer."""
from __future__ import annotations

import importlib.util
import itertools
import json
from pathlib import Path
import random
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from fastunknot import Diagram, ScanLimit, alexander_polynomial, khovanov_rank, recognize
from fastunknot.alexander import alexander_matrix, determinant, evaluate
from fastunknot.decompose import connected_sum, factor_diagram, close_part
from fastunknot.filters import (PRIME, FilterLimit, _alexander_minor, bracket_evaluation,
                               determinant_mod, modular_alexander)
from fastunknot.scan import (ScanComplex, best_scan_order, circles, compose, inverse,
                            scan_order, _compose_uncached)
from fastunknot.simplify import descending_start, legal_moves, simplify
from test_fastunknot import reference_reduced_rank, one_component, load

# Load the preserved original under a different package name. Internal imports
# remain relative, so it cannot accidentally call the accelerated modules.
spec = importlib.util.spec_from_file_location(
    'original_fastunknot', ROOT / 'baseline/fastunknot/__init__.py',
    submodule_search_locations=[str(ROOT / 'baseline/fastunknot')])
BASE = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = BASE
spec.loader.exec_module(BASE)
from original_fastunknot.scan import scan_order as old_order
from original_fastunknot.scan import khovanov_rank as old_rank
from original_fastunknot.simplify import descending_start as old_descending


def random_knots(count=100, maximum=8, seed=20260918):
    rng = random.Random(seed)
    out = []
    while len(out) < count:
        strands = rng.choice([2, 3, 4, 5])
        length = rng.randint(max(1, strands - 1), maximum)
        word = [rng.choice([-1, 1]) * rng.randrange(1, strands) for _ in range(length)]
        if one_component(strands, word):
            out.append(Diagram.from_braid(strands, word))
    return out


def direct_bracket(d, modulus=PRIME, a=2):
    """Independent complete state sum: DSU on edge labels, no scan/glue code."""
    n = d.crossings
    inv = pow(a, -1, modulus)
    delta = (-a*a - inv*inv) % modulus
    if not n:
        return delta
    total = 0
    for bits in range(1 << n):
        parent = list(range(2*n))
        def find(x):
            while parent[x] != x:
                x = parent[x]
            return x
        for i, (p, q, r, s) in enumerate(d.pd):
            pairs = ((p, s), (q, r)) if bits >> i & 1 else ((p, q), (r, s))
            for x, y in pairs:
                parent[find(x)] = find(y)
        loops = len({find(x) for x in range(2*n)})
        exponent = n - 2*bits.bit_count()
        total += pow(a, exponent, modulus) * pow(delta, loops, modulus)
    return total * pow(-pow(a, 3, modulus), -d.writhe(), modulus) % modulus


def verify_descending(d, dart):
    if not d.crossings:
        return True
    alpha = d.alpha()
    visited = set()
    here = dart
    for _ in range(2*d.crossings):
        if here//4 not in visited and here % 2 == 0:
            return False
        visited.add(here//4)
        here = alpha[4*(here//4) + (here+2) % 4]
    return here == dart and len(visited) == d.crossings


class AccelerationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.diagrams = random_knots(120)

    def test_120_dense_cube_comparisons(self):
        for i, d in enumerate(self.diagrams):
            with self.subTest(i=i):
                exact = reference_reduced_rank(d)
                self.assertEqual(khovanov_rank(d.pd, factor=False)['reduced_rank'], exact)
                self.assertEqual(khovanov_rank(d.pd)['reduced_rank'], exact)

    def test_50_original_backend_degree_comparisons(self):
        for d in self.diagrams[:50]:
            old = old_rank(d.pd)
            new = khovanov_rank(d.pd, factor=False)
            self.assertEqual(old['by_degree'], new['by_degree'])

    def test_24_d_squared_checks(self):
        for d in self.diagrams[:24]:
            khovanov_rank(d.pd, factor=False, check_d_squared=True)

    def test_500_greedy_and_descending_comparisons(self):
        for d in random_knots(500, 30, 733):
            baseline = BASE.Diagram.from_pd(d.pd)
            for start in {0, d.crossings//2, d.crossings-1}:
                self.assertEqual(scan_order(d.pd, start), old_order(d.pd, start))
            dart = descending_start(d)
            self.assertEqual(dart is not None, old_descending(baseline) is not None)
            if dart is not None:
                self.assertTrue(verify_descending(d, dart))

    def test_independent_bracket_120_diagrams_three_rings(self):
        for d in self.diagrams:
            for modulus, a in ((PRIME, 2), (101, 3), (15, 2)):
                value = bracket_evaluation(d, modulus=modulus, a=a)['value']
                self.assertEqual(value, direct_bracket(d, modulus, a))

    def test_bracket_moves_mirror_and_pd_half_turns(self):
        rng = random.Random(99)
        for d in self.diagrams[:60]:
            rows = [tuple(row[2:] + row[:2]) if rng.randrange(2) else row for row in d.pd]
            rng.shuffle(rows)
            moved = Diagram.from_pd(rows)
            self.assertEqual(moved.writhe(), d.writhe())
            original = bracket_evaluation(d)['value']
            self.assertEqual(bracket_evaluation(moved)['value'], original)
            self.assertEqual(bracket_evaluation(d.mirror(), a=pow(2, -1, PRIME))['value'], original)
            reduced, _ = simplify(d)
            self.assertEqual(bracket_evaluation(reduced)['value'], original)
            self.assertEqual(alexander_polynomial(moved), alexander_polynomial(d))
        # Markov stabilizations and braid relations, with the same closure.
        for sign in (-1, 1):
            for word in ([1, 1, 1], [-1, -1, -1], [1, -1, 1]):
                base = Diagram.from_braid(2, word)
                moved = Diagram.from_braid(3, list(word) + [sign*2])
                self.assertEqual(bracket_evaluation(base)['value'], bracket_evaluation(moved)['value'])
        for tail in ([1], [-1], [2], [-2], [1, 2, 1]):
            p = [1, 2, 1] + list(tail)
            q = [2, 1, 2] + list(tail)
            if one_component(3, p):
                self.assertEqual(bracket_evaluation(Diagram.from_braid(3, p))['value'],
                                 bracket_evaluation(Diagram.from_braid(3, q))['value'])

    def test_numeric_alexander_matches_polynomial_minors(self):
        self.assertTrue(all(PRIME % d for d in range(2, 31624)))
        for d in self.diagrams:
            matrix = alexander_matrix(d)
            raw = determinant([[p for p in row[:-1]] for row in matrix[:-1]])
            for t in (-1, 2, pow(2, -1, PRIME)):
                numeric = determinant_mod(_alexander_minor(d, t, PRIME))
                self.assertEqual(numeric, evaluate(raw, t) % PRIME)
            if reference_reduced_rank(d) == 1:
                self.assertFalse(modular_alexander(d)['obstruction'])
        for name in ('conway.json', 'kinoshita_terasaka.json', 'hard_unknot_8.json'):
            self.assertFalse(modular_alexander(load(name))['obstruction'])

    def test_all_local_units_on_three_arcs(self):
        matching = frozenset(frozenset((2*i, 2*i+1)) for i in range(3))
        arcs = sorted(matching, key=min)
        monomials = [frozenset(arcs[i] for i in range(3) if bits >> i & 1)
                     for bits in range(1, 8)]
        one = {frozenset()}
        for bits in range(128):
            f = one | {monomials[i] for i in range(7) if bits >> i & 1}
            self.assertEqual(inverse(f, matching), f)
            self.assertEqual(compose(f, f, matching, matching, matching), one)
            self.assertEqual(_compose_uncached(f, f, matching, matching, matching), one)
            inv = inverse(f, matching)
            inv.clear()
            self.assertTrue(f)

    def test_200_general_compositions_and_cache_aliasing(self):
        rng = random.Random(412)
        matchings = [frozenset(map(frozenset, pairs)) for pairs in
                     [((0,1),(2,3),(4,5)), ((0,1),(2,5),(3,4)),
                      ((0,3),(1,2),(4,5)), ((0,5),(1,2),(3,4)),
                      ((0,5),(1,4),(2,3))]]
        for _ in range(200):
            a, b, c = [rng.choice(matchings) for _ in range(3)]
            def morph(x, y):
                keys = sorted(set(circles(x, y).values()), key=lambda v: sorted(v))
                return {frozenset(keys[i] for i in range(len(keys)) if mask >> i & 1)
                        for mask in range(1 << len(keys)) if rng.randrange(2)}
            f, g = morph(a,b), morph(b,c)
            expected = _compose_uncached(f,g,a,b,c)
            actual = compose(f,g,a,b,c)
            self.assertEqual(actual, expected)
            actual.clear()
            self.assertEqual(compose(f,g,a,b,c), expected)

    def test_connected_sums_rank_degree_and_trace(self):
        choices = [Diagram.from_braid(2, [1]), load('trefoil.json'), load('figure_eight.json')]
        for a, b in itertools.product(choices, repeat=2):
            d = connected_sum(a,b)
            factors, trace = factor_diagram(d)
            self.assertGreaterEqual(len(factors), 2)
            raw = khovanov_rank(d.pd, factor=False)
            factored = khovanov_rank(d.pd)
            self.assertEqual(raw['by_degree'], factored['by_degree'])
            self.assertEqual(factored['reduced_rank'], reference_reduced_rank(d))
            for step in trace:
                local = Diagram.from_pd(step['pd'])
                for part in ('first','second'):
                    close_part(local, tuple(step[part]), tuple(step['edges']))
        c = load('conway.json')
        square = connected_sum(c,c.mirror())
        self.assertEqual(khovanov_rank(square.pd)['reduced_rank'], 33**2)
        self.assertEqual(recognize(square).status, 'KNOTTED')
        self.assertFalse(legal_moves(square))

    def test_collisions_caps_and_invalid_budgets(self):
        d = load('trefoil.json')
        self.assertFalse(bracket_evaluation(d, a=1)['obstruction'])
        with self.assertRaises(FilterLimit):
            bracket_evaluation(d, max_states=1)
        r = recognize(d, use_reduction=False, use_descending=False,
                      use_alexander=False, use_factorization=False, jones_max_states=1)
        self.assertEqual(r.status, 'KNOTTED')
        self.assertEqual(r.method, 'reduced-khovanov-F2-scan')
        self.assertIn('skipped', r.evidence['jones_modular'])
        self.assertEqual(recognize(d, seconds=0).status, 'UNKNOWN')
        for t in (-1, float('nan'), float('inf')):
            with self.assertRaises(ValueError):
                recognize(d, seconds=t)
            with self.assertRaises(ValueError):
                khovanov_rank(d.pd, seconds=t)
        for bad in ([0,0,1], [-1,1,2], [0,1], [True,1,2]):
            with self.assertRaises(ValueError):
                khovanov_rank(d.pd, order=bad)
            with self.assertRaises(ValueError):
                bracket_evaluation(d, order=bad)
        for modulus, a in ((1,2), (4,2)):
            with self.assertRaises(ValueError):
                bracket_evaluation(d, modulus=modulus, a=a)


if __name__ == '__main__':
    unittest.main()
