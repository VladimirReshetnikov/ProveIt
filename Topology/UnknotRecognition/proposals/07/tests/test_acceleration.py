"""Regression/property tests for all acceleration layers and correctness repairs."""
from __future__ import annotations
from copy import deepcopy
import json
from pathlib import Path
import random
import sys
import unittest
from itertools import product
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from fastunknot import Diagram, recognize, alexander_polynomial
from fastunknot.factor import decompose, replay_decomposition, factorized_khovanov_rank
from fastunknot.jones import jones_modular, verify_jones_witness, JonesLimit
from fastunknot.scan import (scan_order, khovanov_rank, compose, inverse, ScanLimit,
                            _compose_reference, _compose_cached, circles, glue, clear_caches)
from fastunknot.simplify import descending_start, simplify
from baseline.fastunknot.scan import scan_order as old_order
from baseline.fastunknot.simplify import descending_start as old_descending
from tools.common import load, connected_sum, power_sum
from test_inherited import reference_reduced_rank, one_component


def random_diagrams(count, seed=510):
    rng = random.Random(seed)
    found = 0
    while found < count:
        strands = rng.choice([2, 3, 4])
        word = [rng.choice((-1, 1)) * rng.randrange(1, strands)
                for _ in range(rng.randrange(1, 10))]
        if one_component(strands, word):
            found += 1
            yield Diagram.from_braid(strands, word)


def dense_jones(d, modulus=1_000_000_007, A=2):
    """Independent 2^n state sum: no frontier transitions or cobordism routines."""
    if not d.crossings:
        return 1
    delta = -(A*A + pow(A, -2, modulus)) % modulus
    answer = 0
    for bits in product((0, 1), repeat=d.crossings):
        parent = list(range(2*d.crossings))
        def find(x):
            while parent[x] != x:
                x = parent[x]
            return x
        for row, bit in zip(d.pd, bits):
            a, b, c, e = row
            pairs = ((a, e), (b, c)) if bit else ((a, b), (c, e))
            for x, y in pairs:
                parent[find(x)] = find(y)
        loops = len({find(x) for x in parent})
        exponent = d.crossings - 2*sum(bits)
        answer += pow(A, exponent, modulus) * pow(delta, loops-1, modulus)
    return answer * pow(-pow(A, 3, modulus), -d.writhe(), modulus) % modulus


class AccelerationTests(unittest.TestCase):
    def test_heap_matches_original_every_start(self):
        for d in random_diagrams(100):
            for start in range(d.crossings):
                self.assertEqual(scan_order(d.pd, start), old_order(d.pd, start))

    def test_linear_descending_matches_original(self):
        for d in random_diagrams(200):
            self.assertEqual(descending_start(d) is not None,
                             old_descending(d) is not None)

    def test_invalid_scan_orders_and_budgets(self):
        d = load('trefoil.json')
        for order in ([0], [0, 0, 1], [0, 1, 3], [0, 1, True]):
            with self.assertRaises(ValueError):
                khovanov_rank(d.pd, order=order)
            with self.assertRaises(ValueError):
                jones_modular(d, order=order)
        for seconds in (-1, float('nan'), float('inf')):
            with self.assertRaises(ValueError):
                recognize(d, seconds=seconds)
        self.assertEqual(recognize(d, seconds=0).status, 'UNKNOWN')
        with self.assertRaises(ScanLimit):
            khovanov_rank(d.pd, seconds=0)

    def test_involutory_units_exhaustively(self):
        pairs = [frozenset((2*i, 2*i+1)) for i in range(3)]
        m = frozenset(pairs)
        terms = [frozenset(pairs[i] for i in range(3) if mask >> i & 1)
                 for mask in range(8)]
        for mask in range(128):
            f = {terms[0]} | {terms[i+1] for i in range(7) if mask >> i & 1}
            self.assertEqual(inverse(f, m), f)
            self.assertEqual(_compose_reference(f, f, m, m, m), {frozenset()})

    def test_cached_algebra_and_owned_results(self):
        a = frozenset((frozenset((0, 1)), frozenset((2, 3))))
        b = frozenset((frozenset((0, 3)), frozenset((1, 2))))
        for source, middle, target in product((a, b), repeat=3):
            ft = list(set(circles(source, middle).values()))
            gt = list(set(circles(middle, target).values()))
            f = {frozenset(), frozenset(ft)}
            g = {frozenset(), frozenset(gt)}
            expected = _compose_reference(f, g, source, middle, target)
            actual = compose(f, g, source, middle, target)
            self.assertEqual(actual, expected)
            actual.clear()
            self.assertEqual(compose(f, g, source, middle, target), expected)
        self.assertEqual(circles.cache_info().maxsize, 8192)
        self.assertEqual(glue.cache_info().maxsize, 8192)
        self.assertEqual(_compose_cached.cache_info().maxsize, 32768)
        clear_caches()
        self.assertEqual(_compose_cached.cache_info().currsize, 0)

    def test_both_pivots_against_dense_cube(self):
        for d in random_diagrams(100, seed=10):
            expected = reference_reduced_rank(d)
            for pivot in ('fill', 'lifo'):
                got = khovanov_rank(d.pd, pivot_strategy=pivot, check_d_squared=True)
                self.assertEqual(got['reduced_rank'], expected)

    def test_modular_frontier_against_dense_state_sum(self):
        rng = random.Random(80)
        for d in random_diagrams(160):
            order = list(range(d.crossings))
            rng.shuffle(order)
            for A in (2, 3):
                self.assertEqual(jones_modular(d, A=A, order=order)['value'], dense_jones(d, A=A))

    def test_jones_does_not_reject_known_unlinks_and_unknots(self):
        for d in random_diagrams(100):
            if reference_reduced_rank(d) == 1:
                self.assertEqual(jones_modular(d)['value'], 1)
        for filename in ('hard_unknot_8.json', 'unknot_braid40.json', 'grid_scrambled_unknot.json'):
            self.assertEqual(jones_modular(load(filename))['value'], 1)

    def test_pd_half_turn_writhe_repair(self):
        # The baseline fails this elementary presentation invariance. Alexander
        # needs the actual incoming under-arc when using the repaired sign.
        rng = random.Random(990)
        for d in random_diagrams(100):
            pd = [row[2:] + row[:2] if rng.randrange(2) else row for row in d.pd]
            rotated = Diagram.from_pd(pd)
            self.assertEqual(d.writhe(), rotated.writhe())
            self.assertEqual(alexander_polynomial(d), alexander_polynomial(rotated))
            self.assertEqual(jones_modular(d)['value'], jones_modular(rotated)['value'])
            self.assertEqual(d.writhe(), -d.mirror().writhe())

    def test_jones_witness_and_tampering(self):
        d = load('conway.json')
        w = jones_modular(d)
        self.assertTrue(verify_jones_witness(d, w))
        for key in ('value', 'writhe', 'delta'):
            bad = dict(w)
            bad[key] += 1
            self.assertFalse(verify_jones_witness(d, bad))
        self.assertFalse(verify_jones_witness(load('hard_unknot_8.json'), w))
        for p, A in ((4, 2), (17, 2)):
            with self.assertRaises(ValueError):
                jones_modular(d, modulus=p, A=A)
        self.assertEqual(jones_modular(load('hard_unknot_8.json'), modulus=35)['value'], 1)

    def test_filter_limits_and_collisions_fall_through(self):
        d = load('conway.json')
        with self.assertRaises(JonesLimit):
            jones_modular(d, max_transitions=1)
        r = recognize(d, jones_max_transitions=1)
        self.assertEqual((r.status, r.method), ('KNOTTED', 'reduced-khovanov-F2-scan'))
        r = recognize(d, use_jones=False, use_alexander=False, max_objects=2)
        self.assertEqual(r.status, 'UNKNOWN')
        # Scanner limits do not veto a valid independent Jones obstruction.
        self.assertEqual(recognize(d, max_objects=2).status, 'KNOTTED')
        self.assertEqual(recognize(load('hard_unknot_8.json')).status, 'UNKNOT')

    def test_connected_sum_rank_and_degree_convolution(self):
        choices = [load('trefoil.json'), load('figure_eight.json'), Diagram.from_braid(2, [1])]
        for a, b in product(choices, repeat=2):
            d = connected_sum(a, b)
            factored = factorized_khovanov_rank(d, check_d_squared=True)
            scanned = khovanov_rank(d.pd, check_d_squared=True)
            self.assertEqual(factored['rank'], scanned['rank'])
            self.assertEqual(factored['by_degree'], scanned['by_degree'])
            self.assertEqual(factored['reduced_rank'], reference_reduced_rank(d))

    def test_factorization_replay_and_tampering(self):
        d = power_sum(load('trefoil.json'), 5)
        leaves, cuts = decompose(d)
        self.assertEqual(len(leaves), 5)
        self.assertEqual(dict(leaves), replay_decomposition(d, cuts))
        bad = deepcopy(cuts)
        bad[0]['cut_edges'][0] = bad[0]['cut_edges'][1]
        with self.assertRaises(ValueError):
            replay_decomposition(d, bad)
        self.assertEqual(sum(x.crossings for _, x in leaves), d.crossings)

    def test_large_factored_rank(self):
        d = power_sum(load('conway.json'), 12)
        r = factorized_khovanov_rank(d)
        self.assertEqual(r['reduced_rank'], 33**12)
        self.assertEqual(len(r['factors']), 12)

    def test_factorized_recognition_without_polynomial_filters(self):
        d = power_sum(load('conway.json'), 4)
        r = recognize(d, use_jones=False, use_alexander=False)
        self.assertEqual((r.status, r.method), ('KNOTTED', 'connected-sum'))
        self.assertEqual(len(r.evidence['decomposition']['factors']), 1)
        u = power_sum(load('hard_unknot_8.json'), 3)
        self.assertEqual(recognize(u).status, 'UNKNOT')

    def test_pipeline_defaults_against_independent_cube(self):
        for d in random_diagrams(120, seed=109):
            expected = 'UNKNOT' if reference_reduced_rank(d) == 1 else 'KNOTTED'
            self.assertEqual(recognize(d).status, expected)

    def test_hard_36_crossing_rank_and_d_squared(self):
        d = load('random5_36.json')
        r = khovanov_rank(d.pd, seconds=30, check_d_squared=True)
        self.assertEqual(r['reduced_rank'], 2949)


if __name__ == '__main__':
    unittest.main()
