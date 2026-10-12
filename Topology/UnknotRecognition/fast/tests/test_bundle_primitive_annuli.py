"""Source primitive families, simultaneous gluing, and independent hostile replay."""
from contextlib import ExitStack
from copy import deepcopy
import json
from pathlib import Path
import random
import unittest
from unittest.mock import patch

from fastunknot.bundle_primitive_annuli_verify import replay_primitive_bundle_annuli
from fastunknot.integer_codec import json_safe
from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
from normal_orbit_research.fixtures import layered_torus
from tests.test_normal_surface_orbits import relabel


class BundlePrimitiveAnnuliTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.bank = json.loads((Path(__file__).parents[1] /
                              'marked_parallelity_research/corpus.json').read_text())['cases']
        cls.case = next(c for c in cls.bank if c['id'] == 'fibonacci_lst_05/mixed')
        cls.raw, cls.rows = cls.case['triangulation'], cls.case['coordinates']
        cls.result = normal_cut_handlebodies(cls.raw, cls.rows, record_certificate=True)

    def test_multiple_primitive_annuli_and_disks_share_a_census(self):
        a = self.result
        self.assertEqual(a['status'], 'COMPLETE')
        self.assertEqual(a['census']['histogram'],
                         [dict(genus=0, multiplicity=1), dict(genus=2, multiplicity=1)])
        p = a['certificate']
        self.assertEqual(p['schema'], 'normal-cut-handlebodies-v3')
        self.assertTrue(verify_normal_cut_handlebodies(self.raw, self.rows, p))
        family = p['primitive_annuli']['components'][0]
        self.assertEqual(len(family['annular_attachments']), 2)
        self.assertEqual(family['spare_boundary_components'], 1)
        self.assertEqual(family['reduced_genus'], 0)
        self.assertTrue(any(x['cycle_rank'] > 0 for x in a['census']['joined_components']))

    def test_nonorientable_base_and_simultaneous_families(self):
        c = next(c for c in self.bank if c['id'] == 'fibonacci_lst_08/mixed')
        a = normal_cut_handlebodies(c['triangulation'], c['coordinates'], record_certificate=True)
        self.assertEqual(a['status'], 'COMPLETE')
        p = a['certificate']
        self.assertTrue(verify_normal_cut_handlebodies(c['triangulation'], c['coordinates'], p))
        profiles = p['parallelity']['summary']['base_profiles']
        self.assertTrue(any(not profiles[r['base_profile']]['orientable']
                            for r in p['primitive_annuli']['components']))
        self.assertEqual(len(p['primitive_annuli']['components']), 2)

    def test_relabelled_sources_preserve_all_component_genera(self):
        rng = random.Random(852027)
        for _ in range(5):
            raw, rows = relabel(self.raw, self.rows, rng)
            a = normal_cut_handlebodies(raw, rows, record_certificate=True)
            self.assertEqual(a['status'], 'COMPLETE')
            self.assertEqual(a['census']['histogram'], self.result['census']['histogram'])
            self.assertTrue(verify_normal_cut_handlebodies(raw, rows, a['certificate']))

    def test_no_spare_boundary_rejects_bundle_rule_and_unproved_core_fallback(self):
        for name in ('fibonacci_lst_09/mixed',):
            c = next(c for c in self.bank if c['id'] == name)
            a = normal_cut_handlebodies(c['triangulation'], c['coordinates'], record_certificate=True)
            self.assertEqual(a['status'], 'INCONCLUSIVE')
            self.assertEqual(a['reason'], 'annular_core_attachment')
        p = self.result['certificate']
        summary = deepcopy(p['parallelity']['summary'])
        r = p['primitive_annuli']['components'][0]
        summary['base_profiles'][r['base_profile']]['boundary_components'] = len(r['annular_attachments'])
        self.assertIsNone(replay_primitive_bundle_annuli(summary, p['boundary']['skeleton'], p['primitive_annuli']))

    def test_hostile_family_records_and_schema_downgrade(self):
        mutations = [
            lambda p: p['primitive_annuli']['components'].clear(),
            lambda p: p['primitive_annuli']['components'][0].update(base_profile=999),
            lambda p: p['primitive_annuli']['components'][0].update(reduced_genus=1),
            lambda p: p['primitive_annuli']['components'][0].update(spare_boundary_components=True),
            lambda p: p['primitive_annuli']['components'][0]['annular_attachments'].pop(),
            lambda p: p.update(schema='normal-cut-handlebodies-v2'),
            lambda p: p.pop('primitive_annuli'),
            lambda p: p['census']['histogram'][1].update(genus=3),
        ]
        for mutate in mutations:
            p = deepcopy(self.result['certificate'])
            mutate(p)
            self.assertFalse(verify_normal_cut_handlebodies(self.raw, self.rows, p))
        p = deepcopy(self.result['certificate'])
        p.pop('primitive_annuli')
        p['schema'] = 'normal-cut-handlebodies-v2'
        self.assertFalse(verify_normal_cut_handlebodies(self.raw, self.rows, p))

    def test_disabled_producers_hexadecimal_transport_and_budgets(self):
        p = deepcopy(self.result['certificate'])
        p['primitive_annuli']['components'][0]['reduced_genus'] = '+0X0'
        names = ('fastunknot.bundle_primitive_annuli.primitive_bundle_annuli',
                 'fastunknot.normal_cut_handlebodies.primitive_bundle_annuli',
                 'fastunknot.normal_cut_handlebodies.normal_cut_handlebodies',
                 'fastunknot.normal_cut_handlebodies._census')
        with ExitStack() as stack:
            for name in names:
                stack.enter_context(patch(name, side_effect=AssertionError('producer used')))
            self.assertTrue(verify_normal_cut_handlebodies(self.raw, self.rows, p))
        self.assertFalse(verify_normal_cut_handlebodies(self.raw, self.rows, p, max_operations=0))
        self.assertEqual(normal_cut_handlebodies(self.raw, self.rows, max_cycles=0)['status'], 'INCONCLUSIVE')

    def test_binary_multiplicity_and_legacy_versions(self):
        rows = [[(1 << 1024) * x for x in row] for row in self.rows]
        a = normal_cut_handlebodies(self.raw, rows, record_certificate=True)
        self.assertEqual(a['status'], 'COMPLETE')
        p = json.loads(json.dumps(json_safe(a['certificate'])))
        self.assertTrue(verify_normal_cut_handlebodies(self.raw, json_safe(rows), p))
        raw, rows = layered_torus(2)
        p = normal_cut_handlebodies(raw, rows, record_certificate=True)['certificate']
        self.assertEqual(p['schema'], 'normal-cut-handlebodies-v1')
        self.assertTrue(verify_normal_cut_handlebodies(raw, rows, p))
        c = next(c for c in self.bank if c['id'] == 'pilot/fibonacci_lst_02/0')
        p = normal_cut_handlebodies(c['triangulation'], c['coordinates'], record_certificate=True)['certificate']
        self.assertEqual(p['schema'], 'normal-cut-handlebodies-v2')
        self.assertTrue(verify_normal_cut_handlebodies(c['triangulation'], c['coordinates'], p))


if __name__ == '__main__':
    unittest.main()
