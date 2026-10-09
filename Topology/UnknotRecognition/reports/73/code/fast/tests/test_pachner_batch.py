"""Commutation, source geometry, hostile evidence and binary-height tests."""
from copy import deepcopy
from itertools import permutations
import json
import random
import unittest
from unittest.mock import patch

from fastunknot.cocycle_transport import transport_cocycle
from fastunknot.diagram import Diagram
from fastunknot.diagram_exterior import diagram_exterior
from fastunknot.diagram_exterior_verify import verify_diagram_exterior
from fastunknot.integer_codec import json_safe
from fastunknot.normal_cocycle import rank_one_cocycle_seed, CocycleLimit
from fastunknot.normal_surface_geometry import _prepare, NormalOrbitError
from fastunknot.pachner23 import pachner_23
from fastunknot.pachner32 import pachner_32
from fastunknot.pachner_batch import (
    pachner_32_batch, pachner_32_regions, select_disjoint_collapses,
)
from fastunknot.pachner_batch_verify import verify_pachner_32_batch
from normal_orbit_research.fixtures import layered_torus


def inflate_disjoint(raw, heights, count):
    """Inflate disjoint input dual edges, retaining exact original-cell tags."""
    pairs, used = [], set()
    for t, row in enumerate(raw['tetrahedra']):
        for f, record in enumerate(row):
            if record is None:
                continue
            u = record['tetrahedron']
            if t == u or t in used or u in used:
                continue
            pairs.append((t, f, u))
            used.update((t, u))
            break
        if len(pairs) == count:
            break
    if len(pairs) != count:
        raise ValueError('not enough disjoint dual edges in this fixture')
    tags = [('old', i) for i in range(len(raw['tetrahedra']))]
    current, h = raw, heights
    for i, (old_t, f, old_u) in enumerate(pairs):
        t, u = tags.index(('old', old_t)), tags.index(('old', old_u))
        move = pachner_23(current, t, f)
        transport = transport_cocycle(current, h, move['triangulation'], move['certificate'])
        tags = [tag for j, tag in enumerate(tags) if j not in (t, u)]
        tags.extend(('up', i, j) for j in range(3))
        current, h = move['triangulation'], transport['heights']
    sites = [dict(tetrahedron=tags.index(('up', i, 0)), vertices=[0, 1])
             for i in range(count)]
    return current, h, sites


def sequential_in_batch_order(raw, heights, proof, order):
    """Use old producers, then apply the explicit final cell permutation."""
    regions = [{item['tetrahedron']: item['vertices'] for item in rows}
               for rows in proof['regions']]
    tags = [('old', i) for i in range(len(raw['tetrahedra']))]
    current, h = raw, heights
    gains, savings = 0, 0
    for i in order:
        region = regions[i]
        first = min(region)
        site = tags.index(('old', first))
        vertices = [region[first].index(3), region[first].index(4)]
        move = pachner_32(current, site, vertices)
        transport = transport_cocycle(current, h, move['triangulation'], move['certificate'])
        gains += transport['certificate']['euler_jump']
        savings += transport['certificate']['normal_disc_jump']
        tags = [tag for tag in tags if not (tag[0] == 'old' and tag[1] in region)]
        tags.extend(('new', i, j) for j in range(2))
        current, h = move['triangulation'], transport['heights']
    removed = {t for region in regions for t in region}
    desired = [('old', i) for i in range(len(raw['tetrahedra'])) if i not in removed]
    desired.extend(('new', i, j) for i in range(len(regions)) for j in range(2))
    new_index = {tags.index(tag): i for i, tag in enumerate(desired)}
    rows, final_h = [], []
    for tag in desired:
        old_index = tags.index(tag)
        rows.append([None if face is None else dict(
            tetrahedron=new_index[face['tetrahedron']],
            permutation=list(face['permutation'])) for face in current['tetrahedra'][old_index]])
        final_h.append(h[old_index])
    return dict(tetrahedra=rows), final_h, gains, savings


class PachnerBatchTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        raw, _ = layered_torus(12)
        h = rank_one_cocycle_seed(raw)['heights']
        cls.raw, cls.heights, cls.sites = inflate_disjoint(raw, h, 4)
        cls.batch = pachner_32_batch(cls.raw, cls.sites, cls.heights)

    def test_all_twenty_four_orders_and_identified_vertices(self):
        before_vertices = _prepare(self.raw, lambda: None)['vertices']
        self.assertEqual(before_vertices, 1)
        self.assertEqual(self.batch['stats']['moves'], 4)
        self.assertEqual(self.batch['stats']['intermediate_triangulations'], 0)
        for order in permutations(range(4)):
            final, h, euler, pieces = sequential_in_batch_order(
                self.raw, self.heights, self.batch['certificate'], order)
            self.assertEqual(final, self.batch['triangulation'])
            self.assertEqual(h, self.batch['heights'])
            self.assertEqual(euler, self.batch['certificate']['cocycle']['euler_jump'])
            self.assertEqual(pieces, self.batch['certificate']['cocycle']['normal_disc_jump'])
        reverse = pachner_32_batch(self.raw, list(reversed(self.sites)), self.heights)
        self.assertEqual(reverse, self.batch)

    def test_source_bound_exteriors_and_shared_region_faces(self):
        sources = (Diagram.from_braid(2, [1]),
                   Diagram.from_braid(2, [1, 1, 1]),
                   Diagram.from_braid(3, [1, -2, 1, -2]))
        shared_total = 0
        for source in sources:
            initial = diagram_exterior(source)
            self.assertTrue(verify_diagram_exterior(source, initial))
            h = rank_one_cocycle_seed(initial)['heights']
            raw, h, sites = inflate_disjoint(initial, h, 3)
            answer = pachner_32_batch(raw, sites, h)
            owner = {entry['tetrahedron']: i for i, region in
                     enumerate(answer['certificate']['regions']) for entry in region}
            shared_total += sum(face is not None and face['tetrahedron'] in owner
                                and owner[t] != owner[face['tetrahedron']]
                                for t in owner for face in raw['tetrahedra'][t])
            for order in permutations(range(3)):
                final, heights, _, _ = sequential_in_batch_order(raw, h,
                    answer['certificate'], order)
                self.assertEqual(final, answer['triangulation'])
                self.assertEqual(heights, answer['heights'])
        self.assertGreater(shared_total, 0)

    def test_candidate_conflict_bound_and_maximal_selection(self):
        census = pachner_32_regions(self.raw, self.heights)['candidates']
        self.assertGreaterEqual(len(census), 4)
        for strategy in ('first', 'score'):
            selection = select_disjoint_collapses(census, strategy=strategy)
            self.assertLessEqual(selection['stats']['maximum_conflict_degree'], 9)
            self.assertGreaterEqual(10 * selection['stats']['selected'], len(census))
            supports = [{row['tetrahedron'] for row in candidate['region']}
                        for candidate in census]
            chosen = selection['selected_indices']
            for i in range(len(chosen)):
                for j in range(i):
                    self.assertTrue(supports[chosen[i]].isdisjoint(supports[chosen[j]]))
            for i in set(range(len(census))) - set(chosen):
                self.assertTrue(any(not supports[i].isdisjoint(supports[j]) for j in chosen))
            pachner_32_batch(self.raw, selection['sites'], self.heights)

    def test_independent_verifier_and_exact_validation_count(self):
        with patch('fastunknot.pachner_batch.pachner_32_batch', side_effect=AssertionError), \
             patch('fastunknot.pachner_batch._assemble', side_effect=AssertionError), \
             patch('fastunknot.pachner32.pachner_32', side_effect=AssertionError), \
             patch('fastunknot.cocycle_transport.transport_cocycle', side_effect=AssertionError), \
             patch('fastunknot.normal_cocycle.local_coordinates', side_effect=AssertionError):
            self.assertTrue(verify_pachner_32_batch(self.raw, self.batch['triangulation'],
                                                  self.batch['certificate'], self.heights))
        with patch('fastunknot.pachner_batch._prepare', wraps=_prepare) as producer, \
             patch('fastunknot.pachner_batch_verify._prepare', wraps=_prepare) as checker:
            pachner_32_batch(self.raw, self.sites, self.heights)
        self.assertEqual(producer.call_count, 1)
        self.assertEqual(checker.call_count, 2)
        with patch('fastunknot.pachner32._prepare', wraps=_prepare) as old_move, \
             patch('fastunknot.pachner32_verify._prepare', wraps=_prepare) as old_move_check, \
             patch('fastunknot.cocycle_transport._prepare', wraps=_prepare) as old_transport, \
             patch('fastunknot.cocycle_transport_verify._prepare', wraps=_prepare) as old_check:
            sequential_in_batch_order(self.raw, self.heights,
                                       self.batch['certificate'], range(4))
        self.assertEqual(sum(item.call_count for item in
            (old_move, old_move_check, old_transport, old_check)), 8 * 4)

    def test_binary_height_scaling_offsets_and_input_immutability(self):
        scale = 1 << 20000
        huge = [[scale * x + 7 * (t + 1) for x in row]
                for t, row in enumerate(self.heights)]
        saved = deepcopy((self.raw, self.heights, self.sites, huge))
        answer = pachner_32_batch(self.raw, self.sites, huge)
        self.assertEqual(answer['stats']['work'], self.batch['stats']['work'])
        self.assertEqual(answer['heights'], [[scale * x for x in row]
                                            for row in self.batch['heights']])
        self.assertEqual(answer['coordinates'], [[scale * x for x in row]
                                                for row in self.batch['coordinates']])
        wire = json.loads(json.dumps(json_safe(answer['certificate'])))
        source_wire = json.loads(json.dumps(json_safe(huge)))
        self.assertTrue(verify_pachner_32_batch(self.raw, answer['triangulation'],
                                               wire, source_wire))
        self.assertEqual((self.raw, self.heights, self.sites, huge), saved)

    def test_overlapping_legal_stars_are_rejected(self):
        raw, _ = layered_torus(6)
        rng = random.Random(102)
        for _ in range(3):
            sites = [(t, f) for t, row in enumerate(raw['tetrahedra'])
                     for f, entry in enumerate(row)
                     if entry is not None and entry['tetrahedron'] != t]
            t, f = rng.choice(sites)
            raw = pachner_23(raw, t, f)['triangulation']
        candidates = pachner_32_regions(raw)['candidates']
        self.assertEqual(len(candidates), 2)
        regions = [{row['tetrahedron'] for row in candidate['region']}
                   for candidate in candidates]
        self.assertFalse(regions[0].isdisjoint(regions[1]))
        sites = [dict(tetrahedron=item['tetrahedron'], vertices=item['vertices'])
                 for item in candidates]
        with self.assertRaisesRegex(ValueError, 'share a tetrahedron'):
            pachner_32_batch(raw, sites)
        selected = select_disjoint_collapses(candidates)
        self.assertEqual(selected['stats']['selected'], 1)
        pachner_32_batch(raw, selected['sites'])

    def test_malformed_regions_overlap_and_wrong_source(self):
        proof, after = self.batch['certificate'], self.batch['triangulation']
        bad_proofs = [None, {}, dict(proof, extra=0), dict(proof, schema='wrong'),
                      dict(proof, regions=None), dict(proof, regions=[])]
        for field, value in (('tetrahedron', True), ('tetrahedron', -1),
                             ('tetrahedron', 999), ('vertices', [0, 1, 3, 3]),
                             ('vertices', [False, 1, 3, 4]), ('vertices', None)):
            bad = deepcopy(proof)
            bad['regions'][0][0][field] = value
            bad_proofs.append(bad)
        bad = deepcopy(proof)
        bad['regions'][1] = deepcopy(bad['regions'][0])
        bad_proofs.append(bad)
        bad = deepcopy(proof)
        bad['regions'].reverse()
        bad_proofs.append(bad)
        for bad in bad_proofs:
            self.assertFalse(verify_pachner_32_batch(self.raw, after, bad, self.heights))
        with self.assertRaisesRegex(ValueError, 'more than once'):
            pachner_32_batch(self.raw, self.sites + [self.sites[0]], self.heights)
        invalid = deepcopy(self.heights)
        invalid[0][1] += 1
        self.assertFalse(verify_pachner_32_batch(self.raw, after, proof, invalid))
        with self.assertRaises(NormalOrbitError):
            pachner_32_batch(self.raw, self.sites, invalid)
        self.assertFalse(verify_pachner_32_batch(self.raw, after, proof))

    def test_all_retained_and_internal_face_deletions_rejected(self):
        for t, row in enumerate(self.batch['triangulation']['tetrahedra']):
            for f, face in enumerate(row):
                if face is not None:
                    bad = deepcopy(self.batch['triangulation'])
                    bad['tetrahedra'][t][f] = None
                    self.assertFalse(verify_pachner_32_batch(self.raw, bad,
                                      self.batch['certificate'], self.heights))

    def test_mutated_transport_evidence(self):
        for field in ('euler_jump', 'normal_disc_jump'):
            bad = deepcopy(self.batch['certificate'])
            bad['cocycle'][field] += 1
            self.assertFalse(verify_pachner_32_batch(self.raw, self.batch['triangulation'],
                                                    bad, self.heights))
        for field, i, j in (('bipyramid_heights', 0, 1), ('heights', 0, 1),
                            ('coordinates', 0, 0)):
            bad = deepcopy(self.batch['certificate'])
            bad['cocycle'][field][i][j] += 1
            self.assertFalse(verify_pachner_32_batch(self.raw, self.batch['triangulation'],
                                                    bad, self.heights))

    def test_geometry_only_empty_batch_and_limits(self):
        only = pachner_32_batch(self.raw, self.sites)
        self.assertEqual(only['triangulation'], self.batch['triangulation'])
        self.assertTrue(verify_pachner_32_batch(self.raw, only['triangulation'],
                                              only['certificate']))
        for heights in (None, self.heights):
            empty = pachner_32_batch(self.raw, [], heights)
            self.assertEqual(empty['triangulation'], self.raw)
            self.assertTrue(verify_pachner_32_batch(self.raw, self.raw,
                                                  empty['certificate'], heights))
        exact = self.batch['stats']['work']
        self.assertEqual(pachner_32_batch(self.raw, self.sites, self.heights,
                                         max_work=exact), self.batch)
        with self.assertRaises(CocycleLimit):
            pachner_32_batch(self.raw, self.sites, self.heights, max_work=exact - 1)

    def test_arbitrary_callback_exceptions_propagate(self):
        operations = (
            lambda cb: pachner_32_batch(self.raw, self.sites, self.heights, check=cb),
            lambda cb: verify_pachner_32_batch(self.raw, self.batch['triangulation'],
                                               self.batch['certificate'], self.heights, check=cb),
        )
        for operation in operations:
            calls = [0]
            def tick():
                calls[0] += 1
            operation(tick)
            total = calls[0]
            for exception in (RuntimeError, ValueError, NormalOrbitError):
                for stop in (1, total // 2, total):
                    calls[0] = 0
                    def cancel():
                        tick()
                        if calls[0] == stop:
                            raise exception('cancelled')
                    with self.assertRaisesRegex(exception, 'cancelled'):
                        operation(cancel)


if __name__ == '__main__':
    unittest.main()
