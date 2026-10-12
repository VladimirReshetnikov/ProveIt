"""Native-source, literal-path, hostile-proof and binary-size checks."""

from contextlib import ExitStack
from copy import deepcopy
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from fastunknot.integer_codec import encoded_integer, json_safe
from fastunknot.normal_parallelity import normal_cut_parallelity
from fastunknot.normal_parallelity_geometry import _parallelity_geometry
from fastunknot.normal_surface_geometry import _prepare, _coordinates
from fastunknot.parallelity_boundary_words import normal_parallelity_boundary_words
from fastunknot.weighted_orbits import weighted_orbit_histogram
from fastunknot.weighted_orbit_verify import verify_weighted_orbit_certificate
from normal_orbit_research.fixtures import layered_torus

from fastunknot.parallelity_boundary_moments import (normal_parallelity_moment_words, native_projection,
                            moments_from_parallelity_packet, _moment_query, _assemble)
from marked_parallelity_research.moment_literal import literal_gap_lengths
from fastunknot.parallelity_boundary_moments_verify import verify_parallelity_moment_words, verify_parallelity_moment_packet


ROOT = Path(__file__).resolve().parents[1]
BANK = json.loads((ROOT / 'marked_parallelity_research/moment_corpus.json').read_text())['cases']


def geometry(raw, rows):
    source = _prepare(raw, lambda: None)
    return _parallelity_geometry(source, _coordinates(source, rows, lambda: None), lambda: None)


class NativeMomentsTests(unittest.TestCase):
    def checked(self, raw, rows, literal=True):
        produced = normal_parallelity_moment_words(raw, rows, record_certificate=True)
        baseline = normal_parallelity_boundary_words(raw, rows, record_certificate=True)
        four = normal_parallelity_moment_words(raw, rows, codec='four', record_certificate=True)
        self.assertEqual(produced['status'], 'COMPLETE')
        self.assertEqual(native_projection(produced['skeleton']), baseline['skeleton'])
        self.assertTrue(verify_parallelity_moment_words(raw, rows, produced['certificate']))
        self.assertEqual(produced['skeleton'], four['skeleton'])
        self.assertTrue(verify_parallelity_moment_words(raw, rows, four['certificate']))
        if literal:
            expected = literal_gap_lengths(geometry(raw, rows))
            self.assertEqual(produced['skeleton']['gaps'], expected['gaps'])
        return produced

    def test_all_157_native_sources_against_complete_baseline_and_literal_paths(self):
        coverage = dict(cap_only=0, loop_edges=0, positive_gaps=0, point_gaps=0,
                        circle_attachments=0, fibre_flips=0, literal_cases=0)
        for item in BANK:
            with self.subTest(source=item['id']):
                raw, rows = item['triangulation'], item['coordinates']
                g = geometry(raw, rows)
                small = g['corner_points'] <= 100000
                answer = self.checked(raw, rows, literal=small)
                kinds = {p['kind'] for p in g['polygons']}
                coverage['cap_only'] += kinds == {'edge_cap'}
                coverage['circle_attachments'] += answer['skeleton']['circle_attachments']
                coverage['fibre_flips'] += sum(gap['fibre_flip'] for gap in answer['skeleton']['gaps'])
                if small:
                    exact = literal_gap_lengths(g)
                    coverage['literal_cases'] += 1
                    for key in ('loop_edges', 'positive_gaps', 'point_gaps'):
                        coverage[key] += exact[key]
        self.assertEqual(coverage['cap_only'], 5)
        for key in ('positive_gaps', 'point_gaps', 'circle_attachments', 'fibre_flips'):
            self.assertGreater(coverage[key], 0, key)

    def test_one_edge_loop_geometric_regression_distinguished_from_native_source_bank(self):
        # A triangle with its first two adjacent edges identified in reverse
        # is a disk whose remaining boundary is a single loop edge.  This is
        # a geometric query regression, not an authenticated triangulation.
        polygon = dict(id=0, start=0, stop=1, vertices=[{}, {}, {}],
                       corner_starts=[0, 1, 2])
        port = dict(id=0, polygon=0, edge=2, rank=1, core_dimension=0, core_handle=0)
        g = dict(corner_points=3, polygons=[polygon], ports=[port],
                 gluings=[dict(left=0, right=0, left_edge=0, right_edge=1,
                               rank_start=1, rank_stop=2, left_map=[1, -1],
                               right_map=[1, -1], ends_reverse=True, fibre_flip=False)],
                 free_edges=[dict(polygon=0, edge=2, rank_start=1, rank_stop=2,
                                  original_boundary=False, port=0)])
        pairs, weights, shift, _ = _moment_query(g, lambda: None)
        answer = weighted_orbit_histogram(6, pairs, weights, dimension=1,
                                           periodic_rule='aht', record_certificate=True)
        self.assertTrue(verify_weighted_orbit_certificate(6, pairs, weights,
                                                          answer['certificate'], dimension=1))
        skeleton = _assemble(g, answer['histogram'], shift, lambda: None)
        literal = literal_gap_lengths(g)
        self.assertEqual(literal['loop_edges'], 1)
        self.assertEqual(skeleton['gaps'], literal['gaps'])
        self.assertEqual(skeleton['gaps'][0]['unmarked_edges'], 0)
        self.assertEqual(skeleton['boundary_loops'][0]['word'], [1])
        self.assertEqual(skeleton['circle_attachments'], 1)

    def test_layered_multiples_and_one_sided_bases(self):
        for count in (1, 2, 4, 8):
            raw, source = layered_torus(count)
            for multiple in (0, 1, 2, 5):
                self.checked(raw, [[multiple * x for x in row] for row in source])
        raw, _ = layered_torus(1)
        for multiple in (1, 2, 3, 8):
            self.checked(raw, [[0, 0, 0, 0, 0, multiple, 0]])

    def test_canonical_edge_ownership_is_once_per_lift(self):
        for case in (3, 8, 11, 72, 95, 147):
            item = BANK[case]
            g = geometry(item['triangulation'], item['coordinates'])
            _, _, _, owners = _moment_query(g, lambda: None)
            expected = 2 * sum(edge['rank_stop'] - edge['rank_start']
                               for edge in g['free_edges'] if edge['original_boundary'])
            self.assertEqual(sum(owner['stop'] - owner['start'] for owner in owners), expected)
            self.assertEqual(len({(owner['free_edge'], owner['sheet']) for owner in owners}),
                             len(owners))
            self.assertTrue(all(g['free_edges'][owner['free_edge']]['original_boundary']
                                for owner in owners))

    def test_binary_multiplicity_and_independent_checker(self):
        raw, source = layered_torus(2)
        metrics = []
        for bits in (32, 512, 16384):
            rows = [[(1 << bits) * value for value in row] for row in source]
            result = self.checked(raw, rows, literal=False)
            proof = json.loads(json.dumps(json_safe(result['certificate'])))
            disabled = ('fastunknot.parallelity_boundary_moments.normal_parallelity_moment_words',
                        'fastunknot.parallelity_boundary_moments._moment_query', 'fastunknot.parallelity_boundary_moments._decode',
                        'fastunknot.parallelity_boundary_moments._assemble', 'fastunknot.parallelity_boundary_moments._parallelity_geometry',
                        'fastunknot.parallelity_boundary_moments.weighted_orbit_histogram',
                        'fastunknot.normal_parallelity_geometry._parallelity_geometry',
                        'fastunknot.parallelity_boundary_words._queries',
                        'fastunknot.parallelity_boundary_words._skeleton',
                        'fastunknot.weighted_orbits.weighted_orbit_histogram')
            with ExitStack() as stack:
                for name in disabled:
                    stack.enter_context(patch(name, side_effect=AssertionError('producer called')))
                self.assertTrue(verify_parallelity_moment_words(raw, json_safe(rows), proof))
            metrics.append(dict(bits=bits, ports=len(result['skeleton']['ports']),
                                cycles=result['stats']['census']['orbit_cycles'],
                                owner_intervals=result['stats']['compilation']['owner_intervals'],
                                weight_records=result['stats']['compilation']['weight_records']))
        self.assertEqual(len({(r['ports'], r['cycles'], r['owner_intervals'], r['weight_records'])
                              for r in metrics}), 1)

    def test_verified_packet_including_passive_and_cap_only_bases(self):
        passive = 0
        for case in (3, 33, 72, 145, 147, 153):
            item = BANK[case]
            raw, rows = item['triangulation'], item['coordinates']
            packet = normal_cut_parallelity(raw, rows, record_certificate=True)['certificate']
            transported = json.loads(json.dumps(json_safe(packet)))
            result = moments_from_parallelity_packet(raw, rows, transported, record_certificate=True)
            self.assertTrue(verify_parallelity_moment_packet(raw, rows, result['certificate']))
            for interface in result['base_interfaces']:
                passive += interface['multiplicity'] * interface['passive_boundary_components_per_copy']
            bad = deepcopy(result['certificate'])
            if bad['base_interfaces']:
                bad['base_interfaces'][0]['passive_boundary_components_per_copy'] += 1
                self.assertFalse(verify_parallelity_moment_packet(raw, rows, bad))
            bad_source = deepcopy(packet)
            bad_source['input_sha256'] = '0' * 64
            with self.assertRaisesRegex(ValueError, 'source packet'):
                moments_from_parallelity_packet(raw, rows, bad_source)
            if packet['geometry']['free_edges']:
                bad_source = deepcopy(packet)
                bad_source['geometry']['free_edges'][0]['rank_stop'] += 1
                with self.assertRaisesRegex(ValueError, 'source packet'):
                    moments_from_parallelity_packet(raw, rows, bad_source)
        self.assertGreater(passive, 0)

    def test_hostile_boundaries_moments_lengths_and_sources(self):
        raw, rows = layered_torus(4)
        proof = normal_parallelity_moment_words(raw, rows, record_certificate=True)['certificate']
        bad = []
        for field, value in (('schema', 'wrong'), ('codec', 'bad'), ('codec', 'four'),
                             ('input_sha256', '0' * 64),
                             ('skeleton', None), ('census', None)):
            item = deepcopy(proof)
            item[field] = value
            bad.append(item)
        for field in ('fibre_flip', 'old_boundary_present'):
            item = deepcopy(proof)
            item['skeleton']['gaps'][0][field] ^= True
            bad.append(item)
        for value in (True, -1, 10 ** 6, '0x123'):
            item = deepcopy(proof)
            item['skeleton']['gaps'][0]['unmarked_edges'] = value
            bad.append(item)
        item = deepcopy(proof)
        item['skeleton']['boundary_loops'][0]['word'][0] *= -1
        bad.append(item)
        item = deepcopy(proof)
        item['skeleton']['ports'][0]['core_handle'] += 1
        bad.append(item)
        item = deepcopy(proof)
        item['census']['histogram'][-1]['weight'][0] += 1
        bad.append(item)
        item = deepcopy(proof)
        item['census']['histogram'][-1]['orbits'] += 1
        bad.append(item)
        for number, candidate in enumerate(bad):
            with self.subTest(mutation=number):
                self.assertFalse(verify_parallelity_moment_words(raw, rows, candidate))
        changed = [[2 * value for value in row] for row in rows]
        self.assertFalse(verify_parallelity_moment_words(raw, changed, proof))

    def test_budget_boundaries_no_partial_result_and_cancellation(self):
        raw, rows = layered_torus(4)
        answer = normal_parallelity_moment_words(raw, rows, record_certificate=True)
        cycles = answer['stats']['census']['orbit_cycles']
        for cap in (0, cycles - 1):
            partial = normal_parallelity_moment_words(raw, rows, max_cycles=cap, record_certificate=True)
            self.assertEqual(partial['status'], 'INCONCLUSIVE')
            self.assertNotIn('skeleton', partial)
            self.assertNotIn('certificate', partial)
        self.assertEqual(normal_parallelity_moment_words(raw, rows, max_cycles=cycles)['skeleton'],
                         answer['skeleton'])
        proof = answer['certificate']
        size = len(proof['census']['orbit_proof']['operations'])
        self.assertFalse(verify_parallelity_moment_words(raw, rows, proof, max_operations=size - 1))
        self.assertTrue(verify_parallelity_moment_words(raw, rows, proof, max_operations=size))
        class Cancel:
            def __call__(self):
                raise RuntimeError('cancelled')
        for function, arguments in ((normal_parallelity_moment_words, (raw, rows)),
                                    (verify_parallelity_moment_words, (raw, rows, proof))):
            with self.assertRaisesRegex(RuntimeError, 'cancelled'):
                function(*arguments, check=Cancel())


if __name__ == '__main__':
    unittest.main()
