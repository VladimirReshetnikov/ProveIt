"""Core-side primitive annuli: source replay and unsigned passive transport."""
from contextlib import ExitStack
from copy import deepcopy
import json
from pathlib import Path
import random
import unittest
from unittest.mock import patch

from fastunknot.core_handlebody import core_handlebody_certificate
from fastunknot.core_primitive_annuli import core_primitive_annuli
from fastunknot.core_primitive_annuli_verify import replay_core_primitive_annuli
from fastunknot.integer_codec import json_safe
from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
from tests.test_normal_surface_orbits import relabel


def conditional_charts():
    """Synthetic trusted charts for algebraic replay only, not a source cut.

    The passive word traverses h0 in both directions. Its unsigned row is
    (2,1,1), while the real pivot row is (1,1,0). Pivoting at h0 gives
    (0,3,1), whose saturated form is (0,2,1).
    """
    flags = [(0, 0), (1, 0), (2, 0)]
    handles = []
    for i, (a, b) in enumerate(((0, 1), (0, 2), (2, 0))):
        handles.append(dict(id=i, ends=[0, 0], tetrahedron=flags[a][0], face=flags[a][1],
                            target_tetrahedron=flags[b][0], target_face=flags[b][1]))
    core = dict(handles0=[dict(id=0)], handles1=handles, handles3=[],
                handles2=[dict(id=0, cycle=[dict(dimension=0, handle=0),
                    dict(dimension=1, handle=0), dict(dimension=0, handle=0),
                    dict(dimension=1, handle=1)])])
    polygon = dict(kind='edge_cap', vertices=[dict(tetrahedron=t, face=f)
                                            for t, f in (flags[0], flags[1], flags[0], flags[2])],
                   edges=[dict(kind='face_sector') for _ in range(4)])
    g = dict(core=core, polygons=[polygon], ports=[dict(id=i, polygon=0, edge=i,
             core_dimension=1, core_handle=h) for i, h in enumerate((0, 0, 1, 2))])
    summary = dict(base_profiles=[dict(euler_characteristic=0, boundary_components=1,
                                      multiplicity=1, core_ports=[0, 1, 2, 3])])
    skeleton = dict(attachment_components=[dict(kind='circle', word=[1, 2, 3, 4])])
    proof = core_handlebody_certificate(core)['certificate']
    return g, summary, skeleton, core, proof


class CorePrimitiveAnnuliTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.bank = json.loads((Path(__file__).parents[1] /
                              'marked_parallelity_research/corpus.json').read_text())['cases']
        cls.case = next(c for c in cls.bank if c['id'] == 'pilot/fibonacci_lst_05/0')
        cls.raw, cls.rows = cls.case['triangulation'], cls.case['coordinates']
        cls.result = normal_cut_handlebodies(cls.raw, cls.rows, record_certificate=True)

    def test_five_source_families_have_private_core_cocores(self):
        for name in ('pilot/fibonacci_lst_05/0', 'pilot/fibonacci_lst_07/0',
                     'pilot/fibonacci_lst_09/0', 'pilot/lst_4_7/0', 'pilot/lst_7_10/0'):
            c = next(c for c in self.bank if c['id'] == name)
            a = normal_cut_handlebodies(c['triangulation'], c['coordinates'], record_certificate=True)
            self.assertEqual(a['status'], 'COMPLETE')
            self.assertEqual(a['census']['histogram'],
                             [dict(genus=1, multiplicity=1), dict(genus=2, multiplicity=1)])
            self.assertEqual(a['certificate']['schema'], 'normal-cut-handlebodies-v4')
            self.assertTrue(verify_normal_cut_handlebodies(c['triangulation'], c['coordinates'], a['certificate']))

    def test_relabelled_core_chart_owners(self):
        rng = random.Random(852029)
        completed = 0
        for _ in range(5):
            raw, rows = relabel(self.raw, self.rows, rng)
            a = normal_cut_handlebodies(raw, rows, record_certificate=True)
            if a['status'] == 'INCONCLUSIVE':
                # The pre-existing greedy core schedule is label-dependent.
                # Its refusal occurs before passive transport and is not a
                # negative topological conclusion.
                self.assertEqual(a['reason'], 'raw_cancellation_stalled')
                self.assertNotIn('certificate', a)
                continue
            completed += 1
            self.assertEqual(a['census']['histogram'], self.result['census']['histogram'])
            self.assertTrue(verify_normal_cut_handlebodies(raw, rows, a['certificate']))
        self.assertGreaterEqual(completed, 3)

    def test_forged_transport_witnesses_and_schema_downgrades(self):
        mutations = [
            lambda p: p['core_annuli']['curves'].clear(),
            lambda p: p['core_annuli']['curves'][0]['crossings'][0].update(sign=0),
            lambda p: p['core_annuli']['final_rows'][0]['counts'][0].__setitem__(1, 2),
            lambda p: p['core_annuli']['witnesses'][0].update(one_handle=12),
            lambda p: p['core_annuli']['witnesses'][0].update(core_component=999),
            lambda p: p['core_annuli']['witnesses'][0].update(attachment=False),
            lambda p: p['core_annuli']['witnesses'].clear(),
            lambda p: p['core']['cancellations'].pop(),
            lambda p: p['census']['histogram'][0].update(genus=0),
        ]
        for mutate in mutations:
            p = deepcopy(self.result['certificate'])
            mutate(p)
            self.assertFalse(verify_normal_cut_handlebodies(self.raw, self.rows, p))
        p = deepcopy(self.result['certificate'])
        p.pop('core_annuli')
        p['schema'] = 'normal-cut-handlebodies-v2'
        self.assertFalse(verify_normal_cut_handlebodies(self.raw, self.rows, p))

    def test_disabled_producers_hex_transport_and_caps(self):
        p = deepcopy(self.result['certificate'])
        p['core_annuli']['witnesses'][0]['one_handle'] = '+0X4'
        names = ('fastunknot.core_primitive_annuli.core_primitive_annuli',
                 'fastunknot.core_primitive_annuli.source_core_circle',
                 'fastunknot.disk_bundle_absorption.source_core_circle',
                 'fastunknot.normal_cut_handlebodies.core_primitive_annuli',
                 'fastunknot.normal_cut_handlebodies._census')
        with ExitStack() as stack:
            for name in names:
                stack.enter_context(patch(name, side_effect=AssertionError('producer used')))
            self.assertTrue(verify_normal_cut_handlebodies(self.raw, self.rows, p))
        self.assertFalse(verify_normal_cut_handlebodies(self.raw, self.rows, p, max_operations=0))
        self.assertEqual(normal_cut_handlebodies(self.raw, self.rows, max_cycles=0)['status'], 'INCONCLUSIVE')

    def test_binary_multiplicity_and_remaining_failures(self):
        rows = [[(1 << 1024) * x for x in row] for row in self.rows]
        a = normal_cut_handlebodies(self.raw, rows, record_certificate=True)
        self.assertEqual(a['status'], 'COMPLETE')
        p = json.loads(json.dumps(json_safe(a['certificate'])))
        self.assertTrue(verify_normal_cut_handlebodies(self.raw, json_safe(rows), p))
        for name, reason in [('pilot/fibonacci_lst_06/0', 'raw_cancellation_stalled'),
                             ('fibonacci_lst_09/mixed', 'annular_core_attachment')]:
            c = next(c for c in self.bank if c['id'] == name)
            a = normal_cut_handlebodies(c['triangulation'], c['coordinates'])
            self.assertEqual(a['status'], 'INCONCLUSIVE')
            self.assertEqual(a['reason'], reason)

    def test_passive_fill_counts_opposite_directions_without_reduction(self):
        args = conditional_charts()
        proof, owners, _ = core_primitive_annuli(*args)
        self.assertEqual(proof['final_rows'], [dict(attachment=0, counts=[[1, 2], [2, 1]])])
        self.assertEqual(proof['witnesses'], [dict(attachment=0, core_component=0, one_handle=2)])
        self.assertEqual(replay_core_primitive_annuli(*args, proof), owners)
        crossings = proof['curves'][0]['crossings']
        self.assertEqual([x['sign'] for x in crossings[:2]], [1, -1])
        # Removing the private crossing leaves two opposite pairs, not zero.
        args[0]['ports'][3]['core_handle'] = 1
        self.assertIsNone(core_primitive_annuli(*args))
        self.assertIsNone(replay_core_primitive_annuli(*args, proof))

    def test_competing_annuli_cannot_share_a_private_column(self):
        g, s, b, core, proof = conditional_charts()
        g['polygons'].append(deepcopy(g['polygons'][0]))
        g['ports'] += [dict(p, id=p['id'] + 4, polygon=1) for p in g['ports'][:4]]
        s['base_profiles'].append(dict(s['base_profiles'][0], core_ports=[4, 5, 6, 7]))
        b['attachment_components'].append(dict(kind='circle', word=[5, 6, 7, 8]))
        self.assertIsNone(core_primitive_annuli(g, s, b, core, proof))

    def test_independent_endpoint_flag_authentication(self):
        args = conditional_charts()
        proof, _, _ = core_primitive_annuli(*args)
        args[0]['polygons'][0]['vertices'][0]['face'] = 99
        self.assertIsNone(replay_core_primitive_annuli(*args, proof))


if __name__ == '__main__':
    unittest.main()
