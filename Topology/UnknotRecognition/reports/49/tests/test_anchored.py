import copy
from itertools import product
from math import gcd
import random
import unittest
from anchored_unknot import Arena, Source, AnchoredState, replay, BadCertificate, ResourceLimit
from anchored_unknot.fixtures import power_chain, power_star, signed_tree, christoffel
from anchored_unknot.linear_audit import audit_state, determinant, rational_rank
from anchored_unknot.native_adapter import snapshot_native, export_native


class AnchoredTests(unittest.TestCase):
    def fixture(self):
        s = power_star(5, 7, duplicate=True)
        state = AnchoredState(s)
        proof = state.run()
        return s, state, proof

    def test_chain_all_prefix_cofactors(self):
        source = power_chain(9, 3)
        state = AnchoredState(source)
        while len(state.alive) > 1:
            state.apply_planned(state.plan(max_pairs=1))
            audit_state(source, state.images, state.dead)
        self.assertEqual(state.images[9][1], 3 ** 8)
        self.assertTrue(state.rank_one_zero())

    def test_star_linear_rounds(self):
        s, state, proof = self.fixture()
        result = replay(s, proof)
        self.assertEqual(len(proof['steps']), 4)
        self.assertEqual(state.images, result.images)
        self.assertTrue(result.rank_one_zero)
        self.assertFalse(result.needs_torsion_freeness)
        self.assertEqual(len(result.dead), 4)

    def test_nonzero_retained_endpoint(self):
        s = power_chain(5, 2, residual='nonzero')
        p = AnchoredState(s).run()
        self.assertEqual(p['endpoint'], 'rank_one_nonzero')
        self.assertFalse(replay(s, p).rank_one_zero)

    def test_huge_binary_powers_without_expansion(self):
        s = power_chain(12, 1 << 1024)
        state = AnchoredState(s)
        proof = state.run(max_pairs=1)
        result = replay(s, proof)
        self.assertEqual(result.images[12][1].bit_length(), 11 * 1024 + 1)
        self.assertEqual(result.images, state.images)

    def test_negative_powers(self):
        s = power_chain(6, -5)
        state = AnchoredState(s)
        p = state.run(max_pairs=1)
        self.assertEqual(state.images[6][1], (-5) ** 5)
        self.assertTrue(replay(s, p).rank_one_zero)

    def test_random_tree_prefixes(self):
        rng = random.Random(84735)
        for _ in range(80):
            r = rng.randrange(2, 10)
            source = signed_tree([rng.randrange(1, i) for i in range(2, r + 1)],
                                 [rng.choice((-5, -2, -1, 1, 2, 3, 7)) for _ in range(r - 1)])
            state = AnchoredState(source)
            while len(state.alive) > 1:
                batch = state.plan(max_pairs=rng.choice((1, 2, 3)))
                self.assertTrue(batch)
                state.apply_planned(batch)
                audit_state(source, state.images, state.dead)
            proof = state.run()
            self.assertTrue(replay(source, proof).rank_one_zero)

    def test_primitive_nonunit_coordinates(self):
        for p, q in ((2, 3), (3, 5), (5, 8), (8, 13)):
            a = Arena()
            s = Source.from_arena(a, [a.word(christoffel(p, q))], (1, 2))
            state = AnchoredState(s)
            proof = state.run()
            self.assertTrue(replay(s, proof).rank_one_zero)
            self.assertEqual(state.images, {1: (1, q), 2: (1, -p)})
            audit_state(s, state.images, state.dead)

    def test_proper_power_obligation_explicit(self):
        a = Arena()
        root = a.power(a.word(christoffel(3, 5)), 17)
        s = Source.from_arena(a, [root], (1, 2))
        result = replay(s, AnchoredState(s).run())
        self.assertTrue(result.needs_torsion_freeness)
        self.assertTrue(result.rank_one_zero)

    def test_torus_relator_is_not_primitive(self):
        a = Arena()
        s = Source.from_arena(a, [a.word((1, 1, 2, 2, 2))], (1, 2))
        state = AnchoredState(s)
        self.assertEqual(state.plan(), [])
        self.assertEqual(state.run()['endpoint'], 'stalled')

    def test_coherent_singleton_rotations(self):
        for q in range(1, 12):
            w = (1,) * q + (-2,)
            for j in range(len(w)):
                a = Arena()
                s = Source.from_arena(a, [a.word(w[j:] + w[:j])], (1, 2))
                p = AnchoredState(s).run()
                self.assertTrue(replay(s, p).rank_one_zero)

    def test_width_all_small_positive_words(self):
        for n in range(2, 10):
            for word in product((1, 2), repeat=n):
                if len(set(word)) != 2:
                    continue
                a = Arena()
                s = Source.from_arena(a, [a.word(word)], (1, 2))
                state = AnchoredState(s)
                P, Q = word.count(1), word.count(2)
                d = gcd(P, Q); p, q = P // d, Q // d
                h = 0; vals = [0]
                for x in word:
                    h += q if x == 1 else -p
                    vals.append(h)
                self.assertEqual(state.width(s.roots[0], 1, 2, p, q), max(vals) - min(vals))
                proof = state.run()
                replay(s, proof)

    def test_export_literal_word_identity_not_only_group_identity(self):
        a = Arena()
        roots = [a.word((1, 1, -2)), a.word((2, 2, -3)), a.word((3, -2, 1, -1))]
        s = Source.from_arena(a, roots, (1, 2, 3))
        state = AnchoredState(s)
        state.apply_planned(state.plan(max_pairs=1))
        current, out = s.materialize(state.images, state.dead)
        for slot, root in enumerate(s.roots):
            original_arena, original_roots = s.materialize({g: (g, 1) for g in s.generators}, set())
            letters = original_arena.expand(original_roots[slot])
            expected = []
            for x in letters:
                target, k = state.images[abs(x)]; k *= 1 if x > 0 else -1
                expected.extend([target if k > 0 else -target] * abs(k))
            self.assertEqual(current.expand(out[slot]), () if slot in state.dead else tuple(expected))

    def test_export_native_protocol(self):
        source, state, proof = self.fixture()
        target = Arena()
        roots = export_native(source, state.images, state.dead, target)
        direct, d_roots = source.materialize(state.images, state.dead)
        for x, y in zip(roots, d_roots):
            self.assertEqual(target.expand(x), direct.expand(y))
        snapshot = snapshot_native(target, roots, state.alive)
        self.assertEqual(snapshot.generators, tuple(sorted(state.alive)))

    def test_source_serialization_roundtrip(self):
        source, _, _ = self.fixture()
        clone = Source.from_payload(source.payload())
        self.assertEqual(source, clone)
        self.assertEqual(source.digest, clone.digest)

    def test_source_rebinding_rejected(self):
        s, _, p = self.fixture()
        with self.assertRaises(BadCertificate):
            replay(power_star(5, 8, duplicate=True), p)

    def test_extra_fields_rejected(self):
        s, _, p = self.fixture()
        p['torsion_free'] = True
        with self.assertRaises(BadCertificate):
            replay(s, p)

    def test_scalar_forgery(self):
        s, _, p = self.fixture()
        p['steps'][0][0]['vector'][0] = '0x2'
        with self.assertRaises(BadCertificate):
            replay(s, p)

    def test_width_forgery(self):
        s, _, p = self.fixture()
        p['steps'][0][0]['width'] = '0x0'
        with self.assertRaises(BadCertificate):
            replay(s, p)

    def test_endpoint_forgery(self):
        s, _, p = self.fixture()
        p['endpoint'] = 'stalled'
        with self.assertRaises(BadCertificate):
            replay(s, p)

    def test_bool_slot_rejected(self):
        s, _, p = self.fixture()
        p['steps'][0][0]['slot'] = False
        with self.assertRaises(BadCertificate):
            replay(s, p)

    def test_duplicate_slot_rejected(self):
        s, _, p = self.fixture()
        p['steps'][1][0]['slot'] = p['steps'][0][0]['slot']
        with self.assertRaises(BadCertificate):
            replay(s, p)

    def test_duplicate_pair_in_batch_rejected(self):
        s, _, p = self.fixture()
        p['steps'][0].append(copy.deepcopy(p['steps'][0][0]))
        with self.assertRaises(BadCertificate):
            replay(s, p)

    def test_overlong_scalar_rejected_before_integer_conversion(self):
        s, _, p = self.fixture()
        p['steps'][0][0]['vector'][0] = '0x' + 'f' * 100000
        with self.assertRaises(BadCertificate):
            replay(s, p)

    def test_noncannonical_scalar_rejected(self):
        s, _, p = self.fixture()
        p['steps'][0][0]['width'] = '0x07'
        with self.assertRaises(BadCertificate):
            replay(s, p)

    def test_work_limit(self):
        s, _, p = self.fixture()
        with self.assertRaises(ResourceLimit):
            AnchoredState(s, max_work=1).run()
        with self.assertRaises(ResourceLimit):
            replay(s, p, max_work=1)

    def test_external_cancellation(self):
        s, _, _ = self.fixture()
        with self.assertRaises(ResourceLimit):
            AnchoredState(s, cancel=lambda: True).run()

    def test_node_limit_and_expansion_preflight(self):
        with self.assertRaises(ResourceLimit):
            Arena(max_nodes=1).letter(1)
        a = Arena(); root = a.power(a.letter(1), 1 << 100)
        with self.assertRaises(ResourceLimit):
            a.expand(root, cap=100)

    def test_no_normalization_needed(self):
        s, state, p = self.fixture()
        result = replay(s, p)
        a, roots = s.materialize(result.images, set(result.dead))
        self.assertTrue(any(a.lengths[x] > 0 for x in roots))
        self.assertTrue(result.rank_one_zero)

    def test_matrix_only_is_not_a_primitive_certificate(self):
        a = Arena(); source = Source.from_arena(a, [a.word((1, 1, 2, 2, 2))], (1, 2))
        # Linear algebra accepts the kernel (3,-2); the content verifier rejects.
        audit_state(source, {1: (1, 3), 2: (1, -2)}, {0})
        forged = {'format': 'source-anchored-projection-v1', 'source_sha256': source.digest,
                  'steps': [[{'slot': 0, 'pair': [1, 2], 'vector': ['0x2', '0x3'],
                              'exponent': '0x1', 'width': '0x4'}]], 'endpoint': 'rank_one_zero'}
        with self.assertRaises(BadCertificate):
            replay(source, forged)

    def test_empty_rank_one_presentation(self):
        source = Source((1,), (('e',),), (0,))
        self.assertTrue(replay(source, AnchoredState(source).run()).rank_one_zero)

    def test_nonconsecutive_generator_ids(self):
        a = Arena(); s = Source.from_arena(a, [a.word((11, 11, -700))], (11, 700))
        self.assertTrue(replay(s, AnchoredState(s).run()).rank_one_zero)

    def test_invalid_source_dag(self):
        with self.assertRaises(ValueError):
            Source((1,), (('e',), ('c', 1, 0)), (1,))
        with self.assertRaises(ValueError):
            Source((1,), (('e',), ('t', True)), (1,))

    def test_det_and_rank(self):
        self.assertEqual(determinant([]), 1)
        self.assertEqual(determinant([[0, 2], [3, 4]]), -6)
        self.assertEqual(determinant([[1, 2, 3], [2, 4, 6], [1, 0, 1]]), 0)
        self.assertEqual(rational_rank([[1, 2], [2, 4]]), 1)

    def test_verifier_independent_of_producer_helpers(self):
        s, _, proof = self.fixture()
        from unittest.mock import patch
        with patch.object(AnchoredState, 'plan', side_effect=RuntimeError('must not call')), \
             patch.object(AnchoredState, 'width', side_effect=RuntimeError('must not call')), \
             patch.object(AnchoredState, 'apply_planned', side_effect=RuntimeError('must not call')), \
             patch.object(AnchoredState, 'rank_one_zero', side_effect=RuntimeError('must not call')):
            self.assertTrue(replay(s, proof).rank_one_zero)


if __name__ == '__main__':
    unittest.main()
