import copy
import itertools
import random
import unittest
from private_cocore import *
from private_cocore.core import EMPTY, MANY, plus, scale
from private_cocore.atlas import merge, multiply
from private_cocore.native_adapter import query_authenticated_curves
from reference import dense_replay, private_rows


class TransportTests(unittest.TestCase):
    def compare(self, real, n, passive, schedule):
        p = compile_program(real, n, schedule)
        b, live = dense_replay(real, n, passive, schedule, zero_fill_only=True)
        expected = private_rows(b, live)
        cert = produce_certificate(real, n, passive, schedule)
        self.assertEqual(tuple(cert['least_private']), expected)
        self.assertTrue(verify_certificate(real, n, passive, cert))
        self.assertEqual(least_private(p, owners(p, passive), len(passive)), expected)
        return p, b, live

    def test_empty(self): self.compare([], 0, [], [])
    def test_zero_real(self): self.compare([], 3, [{0: 1}, {1: 1}, {}], [])
    def test_zero_passive(self): self.compare([{0: 1, 1: 2}], 2, [], [(0, 0)])
    def test_column_chain(self):
        self.compare([{0: 1, 1: 2}, {1: 1, 2: 1}], 4, [{0: 1, 3: 1}], [(0, 0), (1, 1)])
    def test_mixed_row_column(self):
        self.compare([{0: 1}, {0: 3, 1: 1, 2: 1}], 3,
                     [{0: 1}, {1: 1}, {2: 1}], [(0, 0), (1, 1)])
    def test_same_owner_is_collision(self):
        self.assertEqual(plus(3, 3), MANY)
        self.compare([{0: 1, 1: 1}], 2, [{0: 1, 1: 1}], [(0, 0)])
    def test_different_owner_collision(self):
        self.compare([], 1, [{0: 1}, {0: 1}], [])
    def test_weight_two(self): self.compare([{0: 1, 1: 2}], 2, [{0: 1}], [(0, 0)])
    def test_huge_binary_input(self):
        self.compare([{0: 1, 1: 1 << 10000}], 3, [{0: 1, 2: 1}], [(0, 0)])
    def test_discarded_pivot_seed(self): self.compare([{0: 1}], 2, [{0: 1}], [(0, 0)])
    def test_zero_entries(self): self.compare([{0: 1, 1: 0}], 2, [{1: 1}], [(0, 0)])
    def test_nonzero_fill_rejected(self):
        # The schedule really completes, but cannot use this zero-fill kernel.
        a = [{0: 1, 1: 1}, {0: 1, 2: 1}]
        dense_replay(a, 3, [], [(0, 0), (1, 2)])
        with self.assertRaises(ValueError): compile_program(a, 3, [(0, 0), (1, 2)])
    def test_duplicate_row(self):
        with self.assertRaises(ValueError): compile_program([{0: 1}, {1: 1}], 2, [(0, 0), (0, 1)])
    def test_duplicate_column(self):
        with self.assertRaises(ValueError): compile_program([{0: 1}, {0: 1}], 2, [(0, 0), (1, 0)])
    def test_missing_row(self):
        with self.assertRaises(ValueError): compile_program([{0: 1}], 1, [])
    def test_nonunit_pivot(self):
        with self.assertRaises(ValueError): compile_program([{0: 2}], 1, [(0, 0)])
    def test_negative_rejected(self):
        with self.assertRaises(ValueError): compile_program([{0: -1}], 1, [(0, 0)])
    def test_boolean_rejected(self):
        with self.assertRaises(ValueError): compile_program([{0: True}], 1, [(0, 0)])
    def test_out_of_range(self):
        with self.assertRaises(ValueError): compile_program([{2: 1}], 1, [(0, 0)])
    def test_semimodule_laws(self):
        vals = [EMPTY, MANY, 0, 1, 2]
        for a, b, c in itertools.product(vals, repeat=3):
            self.assertEqual(plus(a, plus(b, c)), plus(plus(a, b), c))
            self.assertEqual(plus(a, b), plus(b, a))
        for a, b in itertools.product(vals, repeat=2):
            for w in range(4):
                self.assertEqual(scale(plus(a, b), w), plus(scale(a, w), scale(b, w)))
    def test_certificate_all_fields_tampering(self):
        a, b, s = [{0: 1, 1: 1}], [{0: 1}], [(0, 0)]
        cert = produce_certificate(a, 2, b, s)
        self.assertTrue(verify_certificate(a, 2, b, cert, require_complete=True))
        for key, value in [('schema', 'old'), ('n_columns', 3), ('n_passive', 2),
                           ('pivots', []), ('least_private', [0])]:
            bad = copy.deepcopy(cert); bad[key] = value
            self.assertFalse(verify_certificate(a, 2, b, bad))
        bad = copy.deepcopy(cert); bad['ignored'] = True
        self.assertFalse(verify_certificate(a, 2, b, bad))
    def test_certificate_source_tampering(self):
        cert = produce_certificate([{0: 1, 1: 1}], 2, [{0: 1}], [(0, 0)])
        self.assertFalse(verify_certificate([{0: 1, 1: 2}], 2, [{0: 1}], cert))
        self.assertFalse(verify_certificate([{0: 1, 1: 1}], 2, [{0: 2}], cert))
    def test_verifier_without_producer(self):
        import private_cocore.core as producer
        from unittest.mock import patch
        c = {'schema': 'private-cocore-owner-v1', 'n_columns': 2, 'n_passive': 1,
             'pivots': [[0, 0]], 'least_private': [1]}
        with patch.object(producer, 'produce_certificate', side_effect=RuntimeError), \
             patch.object(producer, 'compile_program', side_effect=RuntimeError):
            self.assertTrue(verify_certificate([{0: 1, 1: 1}], 2, [{0: 1}], c))
    def test_incomplete_private_family(self):
        c = produce_certificate([], 1, [{0: 2}], [])
        self.assertTrue(verify_certificate([], 1, [{0: 2}], c))
        self.assertFalse(verify_certificate([], 1, [{0: 2}], c, require_complete=True))
    def test_independent_order_confluence(self):
        a, b = [{0: 1, 2: 1}, {1: 1, 3: 1}], [{0: 1}, {1: 1}]
        c1 = produce_certificate(a, 4, b, [(0, 0), (1, 1)])
        c2 = produce_certificate(a, 4, b, [(1, 1), (0, 0)])
        self.assertEqual(c1['least_private'], c2['least_private'])
    def test_choice_dependence(self):
        # Same source, different canceled column -> different surviving witness.
        a, b = [{0: 1, 1: 1}], [{0: 1}]
        self.assertNotEqual(produce_certificate(a, 2, b, [(0, 0)])['least_private'],
                            produce_certificate(a, 2, b, [(0, 1)])['least_private'])
    def test_random_differential(self):
        rng = random.Random(173)
        for _ in range(300):
            m, q = rng.randrange(7), rng.randrange(7)
            n = m + rng.randrange(1, 6)
            a = [{i: 1, **{h: rng.randrange(1, 4) for h in range(i + 1, n)
                           if rng.random() < .3}} for i in range(m)]
            b = [{h: rng.randrange(1, 4) for h in range(n) if rng.random() < .3} for _ in range(q)]
            self.compare(a, n, b, [(i, i) for i in range(m)])
    def test_native_shaped_adapter(self):
        augmented = {'handles1': [{'ends': [0, 0]}, {'ends': [0, 0]}],
                     'handles2': [{'cycle': [{'dimension': 1, 'handle': 0}, {'dimension': 1, 'handle': 1}]}]}
        core = {'forest': [], 'components': [{'id': 0, 'zero_handles': [0]}], 'cancellations': [[0, 0]]}
        curves = [{'attachment': 5, 'crossings': [{'start': 0, 'handle': 0}]}]
        result = query_authenticated_curves(augmented, core, curves)
        self.assertTrue(result['all_private'])
        self.assertEqual(result['witnesses'][0]['one_handle'], 1)


class AtlasTests(unittest.TestCase):
    def test_owner_two_survives_exception(self):
        p = compile_program([], 1, [])
        a = build_atlas(p, [{0: 2}, {0: 1}], 1)
        self.assertEqual(query_atlas(a, {1}), (-1, -1))
        self.assertEqual(query_atlas(a, {0}), (-1, 0))
    def test_overflow(self):
        p = compile_program([], 1, [])
        a = build_atlas(p, [{0: 1}, {0: 1}, {0: 1}], 1)
        self.assertIsNone(a.signatures[0])
        self.assertEqual(query_atlas(a, {0}), (-1, -1, -1))
    def test_zero_times_overflow(self): self.assertEqual(multiply(None, 0), ())
    def test_invalid_budget(self):
        with self.assertRaises(ValueError): build_atlas(compile_program([], 1, []), [], 1)
    def test_invalid_query(self):
        a = build_atlas(compile_program([], 1, []), [{0: 1}], 0)
        with self.assertRaises(ValueError): query_atlas(a, {0})
    def test_shared_pair_search(self):
        a = build_atlas(compile_program([], 1, []), [{0: 1}, {0: 1}], 1)
        r = find_exceptions(a)
        self.assertEqual(r['status'], 'FOUND'); self.assertEqual(len(r['deleted']), 1)
    def test_search_failure_is_not_knot_verdict(self):
        a = build_atlas(compile_program([], 1, []), [{0: 2}, {0: 2}], 1)
        self.assertEqual(find_exceptions(a)['status'], 'NO_SUBFAMILY_WITHIN_BUDGET')
    def test_search_cap(self):
        a = build_atlas(compile_program([], 1, []), [{0: 1}], 0)
        self.assertEqual(find_exceptions(a, node_cap=0)['status'], 'INCONCLUSIVE')
    def test_delete_all(self):
        a = build_atlas(compile_program([], 0, []), [{}, {}], 2)
        self.assertEqual(find_exceptions(a)['status'], 'FOUND')
    def test_exhaustive_atlas_query_vectors(self):
        for vec in itertools.product(range(3), repeat=4):
            b = [{0: x} for x in vec]
            for k in range(4):
                a = build_atlas(compile_program([], 1, []), b, k)
                for size in range(k + 1):
                    for ds in itertools.combinations(range(4), size):
                        expected = private_rows([[x] for x in vec], [0], frozenset(ds))
                        self.assertEqual(query_atlas(a, ds), expected)
    def test_random_search_against_all_subsets(self):
        rng = random.Random(902)
        for _ in range(180):
            q, n = rng.randrange(1, 7), rng.randrange(1, 6)
            b = [{h: rng.randrange(1, 3) for h in range(n) if rng.random() < .45} for _ in range(q)]
            k = rng.randrange(q + 1)
            a = build_atlas(compile_program([], n, []), b, k)
            expected = False
            for size in range(k + 1):
                for ds in itertools.combinations(range(q), size):
                    out = query_atlas(a, ds)
                    expected |= all(h >= 0 or i in ds for i, h in enumerate(out))
            r = find_exceptions(a)
            self.assertEqual(r['status'] == 'FOUND', expected)
    def test_atlas_after_transport(self):
        rng = random.Random(881)
        for _ in range(120):
            m, q, n = 4, 5, 8
            a = [{i: 1, **{h: rng.randrange(1, 4) for h in range(i + 1, n) if rng.random() < .25}} for i in range(m)]
            b = [{h: rng.randrange(1, 3) for h in range(n) if rng.random() < .2} for _ in range(q)]
            p = compile_program(a, n, [(i, i) for i in range(m)])
            atlas = build_atlas(p, b, 2)
            exact, live = dense_replay(a, n, b, p.pivots)
            for size in range(3):
                for ds in itertools.combinations(range(q), size):
                    self.assertEqual(query_atlas(atlas, ds), private_rows(exact, live, frozenset(ds)))


class MatchingTests(unittest.TestCase):
    def test_nonzero_fill_normalization(self):
        a, b = [{0: 1, 1: 1}, {0: 1, 2: 1}], [{2: 1}]
        matching = [(0, 0), (1, 2)]
        exact, live = dense_replay(a, 3, b, matching)
        c = produce_matching_certificate(a, 3, b, matching)
        self.assertEqual(tuple(c['least_private']), private_rows(exact, live))
        self.assertTrue(verify_certificate(a, 3, b, c))
    def test_cycle_rejected(self):
        with self.assertRaises(ValueError):
            normalize_matching([{0: 1, 1: 1}, {0: 1, 1: 1}], 2, [(0, 0), (1, 1)])
    def test_source_zero_fill_created_pivot_unsupported(self):
        a = [{0: 1, 1: 1}, {0: 1}]
        dense_replay(a, 2, [], [(0, 0), (1, 1)])
        with self.assertRaises(ValueError): normalize_matching(a, 2, [(0, 0), (1, 1)])
    def test_all_orders_same_full_counts(self):
        rng = random.Random(771)
        for _ in range(20):
            m, n = 5, 8
            a = [{i: 1, **{h: rng.randrange(1, 4) for h in range(i+1,n) if rng.random()<.5}} for i in range(m)]
            b = [{h: rng.randrange(1, 4) for h in range(n) if rng.random()<.4} for _ in range(4)]
            canonical, live = dense_replay(a,n,b,[(i,i) for i in range(m)])
            for order in itertools.permutations(range(m)):
                got, survivors = dense_replay(a,n,b,[(i,i) for i in order])
                self.assertEqual(survivors,live)
                self.assertEqual(got,canonical)
    def test_source_matching_permutation(self):
        a = [{2:1,0:3},{0:1,1:1}]
        normalized=normalize_matching(a,3,[(1,0),(0,2)])
        self.assertEqual(normalized,((0,2),(1,0)))


if __name__ == '__main__': unittest.main()
