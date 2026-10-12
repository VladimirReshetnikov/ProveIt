"""Focused geometric-contract and source-replay checks for saturated bundles."""

from copy import deepcopy
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from fastunknot.integer_codec import json_safe
from fastunknot.normal_cut_saturated import normal_cut_saturated, saturated_source_census
from fastunknot.normal_cut_saturated_verify import (
    replay_saturated_source_census, verify_normal_cut_saturated,
)


def abstract_bundle(core_genus, boundary_words, *, genus=0, crosscaps=None,
                    core_relations=()):
    """Hand-specified geometric interface model, not a source-normal certificate.

    Words are lists of unsigned old core-handle IDs. Each letter receives an
    individual face-sector chart. These fixtures exercise only the finite
    operator; native source authentication is tested separately below.
    """
    b = len(boundary_words)
    chi = 2-b-2*genus if crosscaps is None else 2-b-crosscaps
    handles1 = [dict(id=h, ends=[0, 0], tetrahedron=h, target_tetrahedron=h,
                    face=0, target_face=1) for h in range(core_genus)]
    handles2 = [dict(id=i, cycle=[dict(dimension=0, handle=0)] +
                    [dict(dimension=1, handle=h) for h in word])
                for i, word in enumerate(core_relations)]
    core = dict(handles0=[dict(id=0)], handles1=handles1,
                handles2=handles2, handles3=[])
    polygons, ports, attachments = [], [], []
    for word in boundary_words:
        symbols = []
        for h in word:
            p = len(ports)
            polygons.append(dict(kind='edge_cap', edges=[dict(kind='face_sector')],
                vertices=[dict(tetrahedron=h, face=0), dict(tetrahedron=h, face=1)]))
            ports.append(dict(id=p, core_dimension=1, core_handle=h, polygon=p, edge=0))
            symbols.append(p+1)
        attachments.append(dict(kind='circle', word=symbols))
    profile = dict(euler_characteristic=chi, boundary_components=b,
        multiplicity=1, orientable=crosscaps is None, product=crosscaps is None,
        genus=genus if crosscaps is None else None, crosscaps=crosscaps,
        core_ports=list(range(len(ports))))
    g = dict(core=core, polygons=polygons, ports=ports)
    summary = dict(base_profiles=[profile], core_euler_characteristic=1-core_genus+len(handles2),
                   bundle_euler_characteristic=chi, attachment_euler_characteristic=0)
    return g, summary, dict(attachment_components=attachments)


class FiniteSaturatedTests(unittest.TestCase):
    def complete(self, model):
        result = saturated_source_census(*model)
        self.assertEqual(result['status'], 'COMPLETE')
        self.assertTrue(replay_saturated_source_census(*model, result['certificate']))
        return result

    def test_disk_special_case(self):
        self.assertEqual(self.complete(abstract_bundle(1, [[0]]))['census']['histogram'],
                         [dict(genus=0, multiplicity=1)])

    def test_punctured_torus_saturated_anchor(self):
        result = self.complete(abstract_bundle(1, [[0]], genus=1))
        self.assertEqual(result['census']['histogram'], [dict(genus=2, multiplicity=1)])
        self.assertEqual(result['certificate']['saturated_bases'][0]['relative_one_handles'], 2)

    def test_mobius_saturated_anchor(self):
        result = self.complete(abstract_bundle(1, [[0]], crosscaps=1))
        self.assertEqual(result['census']['histogram'], [dict(genus=1, multiplicity=1)])

    def test_saturated_trefoil_amalgam_is_not_accepted(self):
        model = abstract_bundle(1, [[0, 0, 0]], crosscaps=1)
        self.assertEqual(saturated_source_census(*model)['status'], 'INCONCLUSIVE')

    def test_annulus_two_distinct_core_handles(self):
        result = self.complete(abstract_bundle(2, [[0], [1]]))
        self.assertEqual(result['census']['histogram'], [dict(genus=2, multiplicity=1)])
        self.assertEqual(len(result['certificate']['cancellations']), 1)

    def test_annular_words_must_be_aggregated(self):
        # Two individually primitive annuli give aggregate coefficient two.
        model = abstract_bundle(1, [[0], [0]])
        self.assertEqual(saturated_source_census(*model)['status'], 'INCONCLUSIVE')

    def test_mixed_core_and_bundle_rows(self):
        result = self.complete(abstract_bundle(2, [[0, 1]], genus=1, core_relations=[[1]]))
        self.assertEqual(result['certificate']['cancellations'], [[1, 0], [0, 1]])
        self.assertEqual(result['census']['histogram'], [dict(genus=2, multiplicity=1)])

    def test_binary_genus_and_hexadecimal_replay(self):
        g = (1 << 16384)+17
        model = abstract_bundle(1, [[0]], genus=g)
        result = self.complete(model)
        self.assertEqual(result['census']['histogram'], [dict(genus=2*g, multiplicity=1)])
        cert = json.loads(json.dumps(json_safe(result['certificate'])))
        self.assertTrue(replay_saturated_source_census(*model, cert))
        self.assertLess(len(json.dumps(cert)), 30000)
        self.assertEqual(result['stats']['incidence'], 1)

    def test_false_relations_and_census_mutations(self):
        model = abstract_bundle(1, [[0]], genus=1)
        proof = self.complete(model)['certificate']
        mutations = []
        q = deepcopy(proof); q['saturated_bases'] = []; mutations.append(q)
        q = deepcopy(proof); q['cancellations'] = []; mutations.append(q)
        q = deepcopy(proof); q['cancellations'][0][1] = True; mutations.append(q)
        q = deepcopy(proof); q['census']['histogram'][0]['genus'] = 0; mutations.append(q)
        q = deepcopy(proof); q['saturated_bases'][0]['relative_one_handles'] = 0; mutations.append(q)
        q = deepcopy(proof); q['forest'] = [0]; mutations.append(q)
        for q in mutations:
            self.assertFalse(replay_saturated_source_census(*model, q))

    def test_source_chart_mutation(self):
        model = abstract_bundle(1, [[0]], genus=1)
        proof = self.complete(model)['certificate']
        g, summary, skeleton = deepcopy(model)
        g['polygons'][0]['edges'][0]['kind'] = 'not_a_face_sector'
        self.assertFalse(replay_saturated_source_census(g, summary, skeleton, proof))

    def test_callback_abort(self):
        def stop():
            raise TimeoutError('stopped')
        with self.assertRaises(TimeoutError):
            saturated_source_census(*abstract_bundle(1, [[0]]), check=stop)

    def test_replay_callback_value_error_propagates(self):
        model = abstract_bundle(1, [[0]], genus=1)
        proof = self.complete(model)['certificate']
        calls = 0

        def stop_inside():
            nonlocal calls
            calls += 1
            if calls == 3:
                raise ValueError('callback cancellation')

        with self.assertRaisesRegex(ValueError, 'callback cancellation'):
            replay_saturated_source_census(*model, proof, check=stop_inside)

    def test_malformed_pivot_tuples_rejected(self):
        model = abstract_bundle(1, [[0]], genus=1)
        proof = self.complete(model)['certificate']
        for pairs in ([[-1, 0]], [[0, -1]], [[0]], [(0, 0)], [[0, 0], [0, 0]]):
            q = deepcopy(proof)
            q['cancellations'] = pairs
            self.assertFalse(replay_saturated_source_census(*model, q))


class NativeSaturatedTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        path = Path(__file__).resolve().parents[1] / 'marked_parallelity_research/corpus.json'
        cls.cases = {c['id']: c for c in json.loads(path.read_text())['cases']}
        cls.case = cls.cases['pilot/fibonacci_lst_05/0']
        cls.result = normal_cut_saturated(cls.case['triangulation'], cls.case['coordinates'],
                                         record_certificate=True)
        if cls.result['status'] != 'COMPLETE':
            raise AssertionError('native saturated fixture did not complete')

    def test_native_nondisk_saturation(self):
        p = self.result['certificate']
        profiles = p['parallelity']['summary']['base_profiles']
        self.assertTrue(any(profiles[r['base_profile']]['euler_characteristic'] != 1
                            for r in p['finite']['saturated_bases']))
        self.assertTrue(verify_normal_cut_saturated(self.case['triangulation'],
                        self.case['coordinates'], p))

    def test_replay_with_producers_disabled(self):
        names = ['normal_cut_saturated.normal_cut_saturated',
                 'normal_cut_saturated.saturated_source_census',
                 'normal_parallelity.normal_cut_parallelity',
                 'parallelity_boundary_words.normal_parallelity_boundary_words']
        patches = [patch('fastunknot.'+name, side_effect=AssertionError(name)) for name in names]
        for p in patches:
            p.start()
        try:
            self.assertTrue(verify_normal_cut_saturated(self.case['triangulation'],
                            self.case['coordinates'], self.result['certificate']))
        finally:
            for p in reversed(patches):
                p.stop()

    def test_outer_schema_and_source_mutations(self):
        proof = self.result['certificate']
        for field in ('schema', 'summary'):
            q = deepcopy(proof)
            if field == 'schema':
                q['schema'] = 'normal-cut-handlebodies-v3'
            else:
                q['parallelity']['summary']['bundle_euler_characteristic'] += 1
            self.assertFalse(verify_normal_cut_saturated(self.case['triangulation'],
                             self.case['coordinates'], q))

    def test_shared_budget_and_hex_transport(self):
        case = self.case
        proof = json.loads(json.dumps(json_safe(self.result['certificate'])))
        self.assertTrue(verify_normal_cut_saturated(case['triangulation'], case['coordinates'], proof))
        self.assertFalse(verify_normal_cut_saturated(case['triangulation'], case['coordinates'],
                                                    proof, max_operations=0))
        result = normal_cut_saturated(case['triangulation'], case['coordinates'], max_cycles=0)
        self.assertEqual(result['status'], 'INCONCLUSIVE')


if __name__ == '__main__':
    unittest.main()
