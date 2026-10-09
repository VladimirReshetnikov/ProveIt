"""Geometric dynamic scores versus full replay, including shared vertices."""
from copy import deepcopy
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from fastunknot.cocycle_peeling import CocyclePeelingState
from fastunknot.cocycle_peeling_verify import verify_peeled_batch_score
from fastunknot.cocycle_transport import transport_cocycle
from fastunknot.normal_cocycle import rank_one_cocycle_seed
from fastunknot.pachner32 import pachner_32
from normal_orbit_research.fixtures import layered_torus
from tests.test_pachner_batch import inflate_disjoint


class CocyclePeelingTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        raw, _ = layered_torus(16)
        h = rank_one_cocycle_seed(raw)['heights']
        cls.raw, cls.heights, cls.sites = inflate_disjoint(raw, h, 6)

    def test_each_singleton_matches_full_old_geometric_replay(self):
        state = CocyclePeelingState(self.raw, self.heights)
        before = state.full_summary()
        for candidate in state.score_candidates()['candidates']:
            move = pachner_32(self.raw, candidate['tetrahedron'], candidate['vertices'])
            transport = transport_cocycle(self.raw, self.heights,
                                          move['triangulation'], move['certificate'])
            after = CocyclePeelingState(move['triangulation'], transport['heights']).full_summary()
            score = candidate['peeling']
            self.assertEqual(score['peeled_euler_gain'], after['peeled_euler']-before['peeled_euler'])
            self.assertEqual(score['peeled_piece_saving'], before['peeled_pieces']-after['peeled_pieces'])
        self.assertTrue(state.audit_index())

    def test_repeated_commits_keep_stable_ids_and_refresh_prefixes(self):
        state = CocyclePeelingState(self.raw, self.heights)
        moves = 0
        for _ in range(15):
            available = state.score_candidates()['candidates']
            if not available:
                break
            selected = available[0]
            score = selected['peeling']
            before_raw, before_h = deepcopy(state.triangulation), deepcopy(state.heights)
            before = state.full_summary()
            answer = state.apply_batch([dict(tetrahedron=selected['tetrahedron'],
                                             vertices=selected['vertices'])])
            self.assertEqual(answer['peeling'], score)
            after = state.full_summary()
            self.assertEqual(after['peeled_euler']-before['peeled_euler'], score['peeled_euler_gain'])
            self.assertEqual(before['peeled_pieces']-after['peeled_pieces'], score['peeled_piece_saving'])
            self.assertGreaterEqual(score['peeled_piece_saving'], 0)
            self.assertTrue(verify_peeled_batch_score(before_raw, before_h,
                answer['triangulation'], answer['certificate'], answer['peeling_certificate']))
            self.assertTrue(state.audit_index())
            moves += 1
        self.assertGreaterEqual(moves, 6)

    def test_whole_batch_collective_replay_and_empty_batch(self):
        state = CocyclePeelingState(self.raw, self.heights)
        before = state.full_summary()
        answer = state.apply_batch(self.sites)
        after = state.full_summary()
        self.assertEqual(after['peeled_euler']-before['peeled_euler'],
                         answer['peeling']['peeled_euler_gain'])
        self.assertTrue(state.audit_index())
        empty = state.apply_batch([])
        self.assertEqual(empty['peeling']['peeled_euler_gain'], 0)
        self.assertTrue(state.audit_index())

    def test_real_geometric_strict_interaction(self):
        fixture = json.loads((Path(__file__).parent/'fixtures/peeled_batch_interaction.json').read_text())
        raw, heights = fixture['before']['triangulation'], fixture['before']['heights']
        first, second = fixture['construction']['first_site'], fixture['construction']['second_site']
        sites = [dict(tetrahedron=site, vertices=[0, 1]) for site in (first, second)]
        gains = []
        for subset in ([sites[0]], [sites[1]], sites):
            state = CocyclePeelingState(raw, heights)
            before = state.full_summary()
            answer = state.apply_batch(subset)
            after = state.full_summary()
            gains.append(answer['peeling']['peeled_euler_gain'])
            self.assertEqual(gains[-1], after['peeled_euler']-before['peeled_euler'])
            self.assertTrue(verify_peeled_batch_score(raw, heights, answer['triangulation'],
                             answer['certificate'], answer['peeling_certificate']))
        self.assertEqual(gains, [1, 1, 0])

    def test_huge_scale_and_independent_consumer(self):
        scale = 1 << 20000
        state = CocyclePeelingState(self.raw, [[scale*x for x in row] for row in self.heights])
        source_h = deepcopy(state.heights)
        answer = state.apply_batch(self.sites)
        with patch('fastunknot.corner_minima.CornerMinimumIndex', side_effect=AssertionError), \
             patch('fastunknot.cocycle_peeling.CocyclePeelingState', side_effect=AssertionError):
            self.assertTrue(verify_peeled_batch_score(self.raw, source_h,
                answer['triangulation'], answer['certificate'], answer['peeling_certificate']))

    def test_corrupted_score_certificates_rejected(self):
        answer = CocyclePeelingState(self.raw, self.heights).apply_batch(self.sites)
        proof = answer['peeling_certificate']
        for field in proof:
            if field == 'schema':
                continue
            bad = dict(proof)
            bad[field] += 1
            self.assertFalse(verify_peeled_batch_score(self.raw, self.heights,
                answer['triangulation'], answer['certificate'], bad))
        bad = dict(proof, unexpected=0)
        self.assertFalse(verify_peeled_batch_score(self.raw, self.heights,
                answer['triangulation'], answer['certificate'], bad))

    def test_cancelled_index_commit_cannot_be_reused(self):
        state = CocyclePeelingState(self.raw, self.heights)
        with patch.object(state.index, '_delete', side_effect=KeyboardInterrupt):
            with self.assertRaises(KeyboardInterrupt):
                state.apply_batch(self.sites)
        with self.assertRaisesRegex(RuntimeError, 'interrupted'):
            state.score_candidates()

    def test_optimal_subbatch_matches_every_subset(self):
        from fastunknot.pachner_batch import select_disjoint_collapses
        state = CocyclePeelingState(self.raw, self.heights)
        census = state.score_candidates()['candidates']
        chosen = select_disjoint_collapses(census)['selected_indices'][:6]
        ground = [census[i] for i in chosen]
        optimum = state.optimal_subbatch(ground)
        controls = []
        for mask in range(1 << len(ground)):
            selected = [ground[i] for i in range(len(ground)) if mask >> i & 1]
            controls.append((state.score_candidate_batch(selected)['peeled_euler_gain'], len(selected)))
        self.assertEqual((optimum['optimal_peeled_euler_gain'], optimum['retained_moves']), max(controls))
        self.assertEqual(optimum['rewarded_interior_vertices'], 0)
        self.assertEqual(optimum['retained_moves'], len(ground))

    def test_optimizer_resolves_real_shared_vertex_interaction(self):
        fixture = json.loads((Path(__file__).parent/'fixtures/peeled_batch_interaction.json').read_text())
        state = CocyclePeelingState(fixture['before']['triangulation'], fixture['before']['heights'])
        candidates = [c for c in state.score_candidates()['candidates'] if c['tetrahedron'] in (24, 27)]
        answer = state.optimal_subbatch(candidates)
        self.assertEqual(answer['full_batch_peeled_euler_gain'], 0)
        self.assertEqual(answer['optimal_peeled_euler_gain'], 1)
        self.assertEqual(answer['retained_moves'], 1)
        self.assertEqual(answer['rewarded_interior_vertices'], 1)
        committed = state.apply_batch(answer['sites'])
        self.assertEqual(committed['peeling']['peeled_euler_gain'], 1)


if __name__ == '__main__':
    unittest.main()
