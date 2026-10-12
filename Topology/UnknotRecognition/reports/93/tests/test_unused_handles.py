"""Independent source replay, topology controls, and geometric ballast families."""

from contextlib import ExitStack
from copy import deepcopy
import importlib.util
import json
from pathlib import Path
import random
import unittest
from unittest.mock import patch

from fastunknot import Diagram
from fastunknot.diagram_exterior import diagram_exterior
from fastunknot.source_handle_reduction import reduce_source_handles
from fastunknot.source_handle_reduction_verify import verify_source_handle_reduction
from normal_orbit_research.fixtures import layered_torus, regina_triangulation

from unused_handles import (
    compile_diagram_initial_core, decompose_unused_handles,
    verify_diagram_initial_core, verify_unused_handle_certificate,
)
from unused_handle_fixtures import boundary_bud_chain, verify_boundary_bud_chain


ROOT = Path(__file__).resolve().parents[1]
CORPUS = json.loads((ROOT / 'data/unused_handles_source_corpus.json').read_text())['records']


def relabel(raw, rng):
    """Independent local-vertex and tetrahedron relabelling of face pairings."""
    count = len(raw['tetrahedra'])
    order = list(range(count))
    rng.shuffle(order)
    permutations = []
    for _ in range(count):
        row = list(range(4))
        rng.shuffle(row)
        permutations.append(row)
    rows = [[None] * 4 for _ in range(count)]
    for tetrahedron, row in enumerate(raw['tetrahedra']):
        old_to_new = permutations[tetrahedron]
        for face, gluing in enumerate(row):
            if gluing is None:
                continue
            target = gluing['tetrahedron']
            transported = [0] * 4
            for vertex in range(4):
                transported[old_to_new[vertex]] = permutations[target][gluing['permutation'][vertex]]
            rows[order[tetrahedron]][old_to_new[face]] = dict(
                tetrahedron=order[target], permutation=transported
            )
    return dict(tetrahedra=rows)


class UnusedHandleTests(unittest.TestCase):
    def checked(self, raw):
        result = decompose_unused_handles(raw)
        self.assertEqual(result['status'], 'DECOMPOSED')
        self.assertTrue(verify_unused_handle_certificate(raw, result['certificate']))
        decomposition = result['decomposition']
        components = decomposition['components']
        self.assertEqual(
            sum(c['euler_characteristic'] for c in components)
            - len(decomposition['unused_handles']), 0
        )
        self.assertEqual(decomposition['cycle_rank'],
                         len(decomposition['unused_handles']) - len(components) + 1)
        return result

    def test_all_saved_sources_agree_with_native_geometric_closure(self):
        for case in CORPUS:
            raw = case['triangulation']
            new = self.checked(raw)['reduction_certificate']
            self.assertTrue(verify_source_handle_reduction(raw, new))
            old = reduce_source_handles(raw, record_certificate=True)['certificate']
            for key in ('moves', 'remaining', 'summary', 'input_sha256'):
                self.assertEqual(new[key], old[key], (case['id'], key))
            self.assertIsNone(new['compressing_disc'])

    def test_diagram_provenance_and_core_admissibility(self):
        samples = [
            (Diagram.from_braid(2, [1]), 'UNKNOT'),
            (Diagram.from_braid(3, [1, -2]), 'UNKNOT'),
            (Diagram.from_braid(2, [1, 1, 1]), 'ADMISSIBLE_CORE'),
            (Diagram.from_braid(3, [1, -2, 1, -2]), 'ADMISSIBLE_CORE'),
        ]
        for diagram, expected in samples:
            result = compile_diagram_initial_core(diagram)
            self.assertEqual(result['status'], expected)
            self.assertTrue(verify_diagram_initial_core(diagram, result['certificate']))
            if expected == 'ADMISSIBLE_CORE':
                core = result['retained_core']
                proof = result['certificate']['unused_handle_certificate']['reduction_certificate']
                indices = {r['one_handle']: r['index']
                           for r in proof['summary']['characteristic_zero_handle_indices']}
                self.assertEqual(core['euler_characteristic'], 0)
                self.assertTrue(all(indices[face] >= 0 for face in core['one_handles']))
                self.assertLess(len(core['zero_handles']), len(result['certificate']['triangulation']['tetrahedra']))

    def test_replay_does_not_call_either_producer(self):
        raw = next(c['triangulation'] for c in CORPUS if c['id'] == 'interior_1_2')
        certificate = self.checked(raw)['certificate']
        names = (
            'unused_handles._incidence_reduction', 'unused_handles._producer_components',
            'unused_handles._source_handles', 'unused_handles.decompose_unused_handles',
            'fastunknot.source_handle_reduction.reduce_source_handles',
            'fastunknot.source_handle_reduction._source_handles',
        )
        with ExitStack() as stack:
            for name in names:
                stack.enter_context(patch(name, side_effect=AssertionError('producer called')))
            self.assertTrue(verify_unused_handle_certificate(raw, certificate))

    def test_forged_components_and_topology_claims_are_rejected(self):
        diagram = Diagram.from_braid(2, [1, 1, 1])
        wrapped = compile_diagram_initial_core(diagram)['certificate']
        raw = wrapped['triangulation']
        certificate = wrapped['unused_handle_certificate']
        mutations = []
        for key, value in (('torus_case', 'cycle'), ('core_component', True)):
            bad = deepcopy(certificate)
            bad[key] = value
            mutations.append(bad)
        bad = deepcopy(certificate)
        bad['decomposition']['cycle_rank'] = True
        mutations.append(bad)
        bad = deepcopy(certificate)
        bad['decomposition']['components'][0]['euler_characteristic'] += 1
        mutations.append(bad)
        bad = deepcopy(certificate)
        bad['decomposition']['components'][0]['zero_handles'].append(100000)
        mutations.append(bad)
        bad = deepcopy(certificate)
        bad['decomposition']['unused_handles'][0]['ends'].reverse()
        # Reversing a non-loop source edge changes its oriented endpoints.
        mutations.append(bad)
        bad = deepcopy(certificate)
        bad['irreducible'] = True
        mutations.append(bad)
        for bad in mutations:
            self.assertFalse(verify_unused_handle_certificate(raw, bad))
        bad = deepcopy(wrapped)
        bad['outcome'] = 'UNKNOT'
        self.assertFalse(verify_diagram_initial_core(diagram, bad))
        self.assertFalse(verify_diagram_initial_core(Diagram.from_braid(2, [1]), wrapped))

    def test_reducible_controls_never_gain_unconditional_ball_claims(self):
        for name in ('solid_torus_sum_rp3', 'solid_torus_sum_s2xs1'):
            raw = next(c['triangulation'] for c in CORPUS if c['id'] == name)
            result = self.checked(raw)
            self.assertEqual(result['torus_case'], 'cycle')
            self.assertEqual(result['decomposition']['cycle_rank'], 1)
            self.assertTrue(all(c['euler_characteristic'] == 1
                                for c in result['decomposition']['components']))
            self.assertNotEqual(result['status'], 'UNKNOT')
            diagram = Diagram.from_braid(2, [1])
            forged = compile_diagram_initial_core(diagram)['certificate']
            forged['triangulation'] = raw
            forged['unused_handle_certificate'] = result['certificate']
            self.assertFalse(verify_diagram_initial_core(diagram, forged))

    def test_unbounded_ballast_leaves_one_fixed_core(self):
        original = diagram_exterior(Diagram.from_braid(2, [1, 1, 1]))
        baseline = self.checked(original)
        baseline_core = baseline['decomposition']['components'][baseline['core_component']]
        for count in (1, 4, 16, 64):
            raw, shellings = boundary_bud_chain(original, count)
            self.assertTrue(verify_boundary_bud_chain(original, raw, shellings))
            result = self.checked(raw)
            core = result['decomposition']['components'][result['core_component']]
            self.assertEqual(core['zero_handles'], baseline_core['zero_handles'])
            self.assertEqual(len(core['one_handles']), len(baseline_core['one_handles']))
            self.assertEqual(len(core['two_handles']), len(baseline_core['two_handles']))
            self.assertEqual(len(result['decomposition']['components']),
                             len(baseline['decomposition']['components']) + count)
            bad = deepcopy(shellings)
            bad['moves'][0]['face'] = (bad['moves'][0]['face'] + 1) % 4
            self.assertFalse(verify_boundary_bud_chain(original, raw, bad))
            bad_source = deepcopy(raw)
            last = shellings['moves'][-1]
            bad_source['tetrahedra'][last['new_tetrahedron']][last['face']]['permutation'][0] = False
            self.assertFalse(verify_boundary_bud_chain(original, bad_source, shellings))
        self.assertFalse(verify_boundary_bud_chain(original, {}, shellings))

    def test_exact_layered_family_avoids_large_cohomology_values(self):
        for size in (1, 4, 16, 64, 128):
            raw, _ = layered_torus(size)
            result = self.checked(raw)
            self.assertEqual(result['torus_case'], 'cycle')
            self.assertEqual(len(result['decomposition']['components']), size)
            self.assertEqual(result['decomposition']['cycle_rank'], 1)
            self.assertTrue(all(len(c['zero_handles']) == 1 for c in result['decomposition']['components']))
        old = reduce_source_handles(raw, record_certificate=True)['certificate']
        values = old['compressing_disc']['boundary_witness']['dual_values']
        self.assertGreater(max(abs(value).bit_length() for value in values), 80)
        self.assertIsNone(result['reduction_certificate']['compressing_disc'])

    def test_local_and_global_relabellings(self):
        rng = random.Random(202610120137)
        for name in ('finite_trefoil', 'finite_figureEight', 'interior_1_2', 'fibonacci_lst_04'):
            raw = next(c['triangulation'] for c in CORPUS if c['id'] == name)
            for _ in range(12):
                self.checked(relabel(raw, rng))

    def test_caps_and_cooperative_cancellation(self):
        raw, _ = layered_torus(16)
        full = self.checked(raw)
        moves = len(full['reduction_certificate']['moves'])
        for cap in (0, moves - 1):
            result = decompose_unused_handles(raw, max_moves=cap)
            self.assertEqual(result['status'], 'INCONCLUSIVE')
            self.assertNotIn('certificate', result)
        self.assertEqual(decompose_unused_handles(raw, max_moves=moves)['decomposition'],
                         full['decomposition'])
        for cap in (True, -1):
            with self.assertRaises(ValueError):
                decompose_unused_handles(raw, max_moves=cap)
        def stop():
            raise RuntimeError('stop requested')
        with self.assertRaisesRegex(RuntimeError, 'stop requested'):
            decompose_unused_handles(raw, check=stop)
        with self.assertRaisesRegex(RuntimeError, 'stop requested'):
            verify_unused_handle_certificate(raw, full['certificate'], check=stop)

    @unittest.skipUnless(importlib.util.find_spec('regina'), 'independent topology oracle')
    def test_regina_solid_torus_and_nonball_controls(self):
        for name in ('fibonacci_lst_04', 'finite_trefoil',
                     'solid_torus_sum_rp3', 'solid_torus_sum_s2xs1'):
            raw = next(c['triangulation'] for c in CORPUS if c['id'] == name)
            tri = regina_triangulation(raw)
            self.assertTrue(tri.isValid())
            self.assertEqual(tri.isSolidTorus(), name == 'fibonacci_lst_04')
        original = diagram_exterior(Diagram.from_braid(2, [1, 1, 1]))
        raw, proof = boundary_bud_chain(original, 16)
        self.assertTrue(verify_boundary_bud_chain(original, raw, proof))
        tri = regina_triangulation(raw)
        self.assertTrue(tri.isValid())
        self.assertFalse(tri.isSolidTorus())


if __name__ == '__main__':
    unittest.main()
