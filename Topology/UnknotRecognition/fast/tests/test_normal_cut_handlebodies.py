"""Actual cut classification, conservative failures, and hostile replay."""

from contextlib import ExitStack
from copy import deepcopy
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from fastunknot.integer_codec import json_safe
from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
from normal_orbit_research.fixtures import layered_torus


class NormalCutHandlebodyTests(unittest.TestCase):
    def test_parallel_meridians_and_empty_cuts(self):
        for t in (1, 2, 3, 4, 8):
            raw, base = layered_torus(t)
            for n in (0, 1, 2, 5):
                rows = [[n * x for x in row] for row in base]
                a = normal_cut_handlebodies(raw, rows, record_certificate=True)
                self.assertEqual(a['status'], 'COMPLETE')
                self.assertTrue(verify_normal_cut_handlebodies(raw, rows, a['certificate']))
                self.assertEqual(a['census']['histogram'],
                                 [dict(genus=0, multiplicity=n)] if n else
                                 [dict(genus=1, multiplicity=1)])

    def test_adjacent_ports_are_one_disk_and_circles_are_excluded(self):
        raw, rows = layered_torus(4)
        a = normal_cut_handlebodies(raw, rows, record_certificate=True)
        skeleton = a['certificate']['boundary']['skeleton']
        self.assertEqual(len(skeleton['ports']), 15)
        self.assertEqual(skeleton['interval_attachments'], 3)
        self.assertEqual(a['census']['joined_components'][0]['genus'], 0)
        bank = json.loads((Path(__file__).parents[1] /
                           'marked_parallelity_research/corpus.json').read_text())['cases']
        c = next(c for c in bank if c['id'] == 'pilot/fibonacci_lst_02/0')
        a = normal_cut_handlebodies(c['triangulation'], c['coordinates'])
        self.assertEqual(a['status'], 'INCONCLUSIVE')
        self.assertEqual(a['reason'], 'annular_core_attachment')

    def test_one_sided_surfaces_can_give_solid_torus_cuts(self):
        raw, _ = layered_torus(1)
        for n in (1, 2, 3, 4, 7):
            a = normal_cut_handlebodies(raw, [[0, 0, 0, 0, 0, n, 0]],
                                       record_certificate=True)
            self.assertEqual(a['status'], 'COMPLETE')
            self.assertTrue(verify_normal_cut_handlebodies(
                raw, [[0, 0, 0, 0, 0, n, 0]], a['certificate']))
            self.assertTrue(all(p['genus'] == 1 for p in a['census']['histogram']))

    def test_huge_binary_census_and_disabled_producers(self):
        raw, base = layered_torus(1)
        n = 1 << 16384
        rows = [[n * x for x in row] for row in base]
        a = normal_cut_handlebodies(raw, rows, record_certificate=True)
        self.assertEqual(a['census']['ball_components'], n)
        proof = json.loads(json.dumps(json_safe(a['certificate'])))
        functions = (
            'fastunknot.normal_cut_handlebodies.normal_cut_handlebodies',
            'fastunknot.normal_cut_handlebodies._census',
            'fastunknot.normal_parallelity.normal_cut_parallelity',
            'fastunknot.parallelity_boundary_words.normal_parallelity_boundary_words',
            'fastunknot.core_handlebody.core_handlebody_certificate',
        )
        with ExitStack() as stack:
            for name in functions:
                stack.enter_context(patch(name, side_effect=AssertionError('producer used')))
            self.assertTrue(verify_normal_cut_handlebodies(raw, json_safe(rows), proof))

    def test_hostile_genus_owner_and_operation_caps(self):
        raw, rows = layered_torus(2)
        a = normal_cut_handlebodies(raw, rows, record_certificate=True)
        proof = a['certificate']
        for key, value in [('schema', 'bad'), ('census', None), ('core', {})]:
            bad = deepcopy(proof)
            bad[key] = value
            self.assertFalse(verify_normal_cut_handlebodies(raw, rows, bad))
        bad = deepcopy(proof)
        bad['census']['histogram'][0]['genus'] = 1
        self.assertFalse(verify_normal_cut_handlebodies(raw, rows, bad))
        bad = deepcopy(proof)
        bad['boundary']['skeleton']['ports'][0]['core_handle'] += 1
        self.assertFalse(verify_normal_cut_handlebodies(raw, rows, bad))
        self.assertFalse(verify_normal_cut_handlebodies(raw, rows, proof, max_operations=0))
        self.assertEqual(normal_cut_handlebodies(raw, rows, max_cycles=0)['status'], 'INCONCLUSIVE')
        self.assertTrue(verify_normal_cut_handlebodies(raw, rows, proof, max_operations=100000))

    def test_false_callable_callback_is_not_ignored(self):
        class Cancel:
            def __bool__(self):
                return False
            def __call__(self):
                raise ValueError('cancelled')
        raw, rows = layered_torus(1)
        with self.assertRaisesRegex(ValueError, 'cancelled'):
            normal_cut_handlebodies(raw, rows, check=Cancel())
        proof = normal_cut_handlebodies(raw, rows, record_certificate=True)['certificate']
        with self.assertRaisesRegex(ValueError, 'cancelled'):
            verify_normal_cut_handlebodies(raw, rows, proof, check=Cancel())

    def test_hexadecimal_core_components_are_decoded_before_graph_replay(self):
        raw, rows = layered_torus(2)
        proof = normal_cut_handlebodies(raw, rows, record_certificate=True)['certificate']
        component = proof['core']['components'][0]
        component['genus'] = hex(component['genus'])
        component['id'] = hex(component['id'])
        component['zero_handles'] = list(map(hex, component['zero_handles']))
        self.assertTrue(verify_normal_cut_handlebodies(raw, rows, proof))
        component['genus'] = '+0X0'
        self.assertTrue(verify_normal_cut_handlebodies(raw, rows, proof))
        component['genus'] = True
        self.assertFalse(verify_normal_cut_handlebodies(raw, rows, proof))
        component['genus'] = '0xnot-an-integer'
        self.assertFalse(verify_normal_cut_handlebodies(raw, rows, proof))


if __name__ == '__main__':
    unittest.main()
