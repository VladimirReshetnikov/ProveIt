"""Authenticated source chains, partial reductions and hostile knot verdicts."""
from copy import deepcopy
import unittest
from unittest.mock import patch

from fastunknot.diagram import Diagram
from fastunknot.diagram_exterior import diagram_exterior
from fastunknot.boundary_shellings import shell_boundary
from fastunknot.normal_surface_geometry import NormalOrbitError
from fastunknot import normal_crushing_chain as chain_module
from fastunknot.normal_crushing_chain import make_crushing_chain, verify_crushing_chain


# Primitive full-matching extreme ray on the native five-tetrahedron boundary
# shelling of the canonical exterior of Diagram.from_pd([]).  It has chi=1;
# its crush leaves one three-ball tetrahedron and no torus component.
SHELLED_UNKNOT_RAY = [
    [0, 0, 0, 0, 1, 0, 0],
    [0, 0, 1, 1, 0, 0, 0],
    [0, 0, 0, 0, 1, 0, 0],
    [0, 0, 0, 0, 1, 0, 0],
    [0, 0, 0, 0, 1, 0, 0],
]

SHELLED_REDUCTION_RAY = [
    [1, 0, 0, 1, 0, 0, 1],
    [1, 1, 1, 1, 0, 0, 0],
    [0, 1, 1, 0, 0, 0, 1],
    [1, 0, 0, 1, 0, 0, 1],
    [0, 1, 1, 0, 0, 0, 1],
]
ONE_TET_TERMINAL_RAY = [[0, 0, 1, 1, 0, 0, 1]]


class CrushingChainTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.diagram = Diagram.from_pd([])
        cls.partial = make_crushing_chain(cls.diagram, [])
        shelled = shell_boundary(diagram_exterior(cls.diagram))
        cls.shelling = {k: shelled[k] for k in ('triangulation', 'moves')}
        cls.terminal = make_crushing_chain(cls.diagram, [SHELLED_UNKNOT_RAY],
                                           shelling=cls.shelling)

    def test_empty_chain_certifies_only_a_source_bound_partial_result(self):
        for diagram in (self.diagram, Diagram.from_braid(2, [1, 1, 1])):
            proof = make_crushing_chain(diagram, [])
            self.assertEqual(set(proof), {'schema', 'input_pd', 'source_triangulation',
                                          'shelling', 'steps', 'status', 'triangulation'})
            self.assertEqual(proof['schema'], 'diagram-crushing-v1')
            self.assertEqual(proof['status'], 'REDUCED')
            self.assertEqual(proof['steps'], [])
            self.assertIsNone(proof['shelling'])
            self.assertEqual(proof['triangulation'], proof['source_triangulation'])
            self.assertEqual(proof['triangulation'], diagram_exterior(diagram))
            self.assertTrue(verify_crushing_chain(diagram, proof))
            bad = deepcopy(proof)
            bad['status'], bad['triangulation'] = 'UNKNOT', None
            self.assertFalse(verify_crushing_chain(diagram, bad))

    def test_shelling_and_final_partial_triangulation_are_both_replayed(self):
        proof = make_crushing_chain(self.diagram, [], shelling=self.shelling)
        self.assertEqual(proof['status'], 'REDUCED')
        self.assertEqual(proof['triangulation'], self.shelling['triangulation'])
        self.assertEqual(len(proof['triangulation']['tetrahedra']), 5)
        self.assertTrue(verify_crushing_chain(self.diagram, proof))
        zero_shelling = dict(triangulation=deepcopy(self.partial['source_triangulation']), moves=[])
        self.assertTrue(verify_crushing_chain(self.diagram,
            make_crushing_chain(self.diagram, [], shelling=zero_shelling)))
        for mutation in ('omit_move', 'duplicate_move', 'wrong_output', 'extra_key', 'bool_move'):
            bad = deepcopy(proof)
            if mutation == 'omit_move':
                bad['shelling']['moves'].pop()
            elif mutation == 'duplicate_move':
                bad['shelling']['moves'].append(bad['shelling']['moves'][0])
            elif mutation == 'wrong_output':
                bad['triangulation'] = deepcopy(proof['source_triangulation'])
            elif mutation == 'extra_key':
                bad['shelling']['trusted'] = True
            else:
                bad['shelling']['moves'][0] = True
            self.assertFalse(verify_crushing_chain(self.diagram, bad), mutation)

    def test_source_and_diagram_binding_cannot_be_replaced_by_valid_torus_geometry(self):
        other = Diagram.from_braid(2, [1, 1, 1])
        self.assertFalse(verify_crushing_chain(other, self.partial))
        self.assertFalse(verify_crushing_chain(other, self.terminal))
        arbitrary_torus = {'tetrahedra': [[
            {'tetrahedron': 0, 'permutation': [1, 2, 3, 0]},
            {'tetrahedron': 0, 'permutation': [3, 0, 1, 2]}, None, None]]}
        bad = deepcopy(self.partial)
        bad['source_triangulation'] = arbitrary_torus
        bad['triangulation'] = deepcopy(arbitrary_torus)
        self.assertFalse(verify_crushing_chain(self.diagram, bad))
        bad = deepcopy(self.partial)
        bad['source_triangulation']['tetrahedra'][0][1] = None
        bad['triangulation'] = deepcopy(bad['source_triangulation'])
        self.assertFalse(verify_crushing_chain(self.diagram, bad))
        invalid = Diagram(((0, 1, 2, 3),))
        self.assertFalse(verify_crushing_chain(invalid, self.partial))

    def test_real_no_torus_terminal_requires_the_whole_chain(self):
        proof = self.terminal
        self.assertEqual(proof['status'], 'UNKNOT')
        self.assertIsNone(proof['triangulation'])
        self.assertEqual(len(proof['steps']), 1)
        self.assertEqual(proof['steps'][0]['schema'], 'normal-ray-crushing-v1')
        self.assertTrue(verify_crushing_chain(self.diagram, proof))
        for mutation in ('remove_step', 'remove_shelling', 'append_step', 'partial_status', 'final_torus'):
            bad = deepcopy(proof)
            if mutation == 'remove_step':
                bad['steps'] = []
            elif mutation == 'remove_shelling':
                bad['shelling'] = None
            elif mutation == 'append_step':
                bad['steps'].append(deepcopy(bad['steps'][0]))
            elif mutation == 'partial_status':
                bad['status'] = 'REDUCED'
            else:
                bad['triangulation'] = deepcopy(self.shelling['triangulation'])
            self.assertFalse(verify_crushing_chain(self.diagram, bad), mutation)
        with self.assertRaises(ValueError):
            make_crushing_chain(self.diagram, [SHELLED_UNKNOT_RAY, SHELLED_UNKNOT_RAY],
                                shelling=self.shelling)

    def test_strict_reduction_and_one_tetrahedron_terminal_are_source_bound(self):
        first = make_crushing_chain(self.diagram, [SHELLED_REDUCTION_RAY], shelling=self.shelling)
        expected = {'tetrahedra': [[None, None,
            {'tetrahedron': 0, 'permutation': [1, 2, 3, 0]},
            {'tetrahedron': 0, 'permutation': [3, 0, 1, 2]}]]}
        self.assertEqual(first['status'], 'REDUCED')
        self.assertEqual(first['triangulation'], expected)
        self.assertTrue(verify_crushing_chain(self.diagram, first))
        final = make_crushing_chain(self.diagram,
            [SHELLED_REDUCTION_RAY, ONE_TET_TERMINAL_RAY], shelling=self.shelling)
        self.assertEqual(final['status'], 'UNKNOT')
        self.assertIsNone(final['triangulation'])
        self.assertEqual(len(final['steps']), 2)
        self.assertTrue(verify_crushing_chain(self.diagram, final))
        for mutation in ('missing_first', 'reverse_steps', 'duplicate_first', 'unreplayed_final'):
            bad = deepcopy(final)
            if mutation == 'missing_first':
                bad['steps'].pop(0)
            elif mutation == 'reverse_steps':
                bad['steps'].reverse()
            elif mutation == 'duplicate_first':
                bad['steps'][1] = deepcopy(bad['steps'][0])
            else:
                bad['status'] = 'REDUCED'
                bad['triangulation'] = deepcopy(expected)
            self.assertFalse(verify_crushing_chain(self.diagram, bad), mutation)

    def test_packet_schema_and_step_validation_are_strict(self):
        proof = self.terminal
        for key in proof:
            bad = deepcopy(proof)
            del bad[key]
            self.assertFalse(verify_crushing_chain(self.diagram, bad), key)
        for bad in (None, [], {}, dict(proof, extra=True)):
            self.assertFalse(verify_crushing_chain(self.diagram, bad))
        for field, value in (('schema', 'wrong'), ('status', True), ('status', 'KNOTTED'),
                             ('steps', tuple(proof['steps'])), ('steps', [{}]),
                             ('steps', [None]), ('source_triangulation', {}),
                             ('input_pd', [[0, 1, 2, 3]]), ('shelling', {})):
            bad = deepcopy(proof)
            bad[field] = value
            self.assertFalse(verify_crushing_chain(self.diagram, bad), field)

    def test_replay_uses_no_source_constructor_sheller_or_chain_producer(self):
        with patch('fastunknot.diagram_exterior.diagram_exterior', side_effect=AssertionError), \
             patch('fastunknot.boundary_shellings.shell_boundary', side_effect=AssertionError), \
             patch('fastunknot.normal_crushing.crush_normal_ray', side_effect=AssertionError), \
             patch('fastunknot.normal_crushing_chain.make_crushing_chain', side_effect=AssertionError):
            self.assertTrue(verify_crushing_chain(self.diagram, self.partial))
            self.assertTrue(verify_crushing_chain(self.diagram, self.terminal))

    def test_verification_and_construction_do_not_mutate_input_records(self):
        shelling = deepcopy(self.shelling)
        coordinates = [deepcopy(SHELLED_UNKNOT_RAY)]
        before = deepcopy((shelling, coordinates))
        proof = make_crushing_chain(self.diagram, coordinates, shelling=shelling)
        self.assertEqual((shelling, coordinates), before)
        saved = deepcopy(proof)
        self.assertTrue(verify_crushing_chain(self.diagram, proof))
        self.assertEqual(proof, saved)

    def test_caller_exceptions_propagate_from_nested_replay(self):
        class Callback:
            def __init__(self, after, error):
                self.after, self.error = after, error
            def __bool__(self):
                return False
            def __call__(self):
                self.after -= 1
                if self.after == 0:
                    raise self.error
        for operation in (
                lambda check: verify_crushing_chain(self.diagram, self.terminal, check=check),
                lambda check: make_crushing_chain(self.diagram, [SHELLED_UNKNOT_RAY],
                                                  shelling=self.shelling, check=check)):
            polls = [0]
            def count():
                polls[0] += 1
            operation(count)
            for error_type in (ValueError, TypeError, KeyError, IndexError, NormalOrbitError, RuntimeError):
                for after in sorted({1, 29, polls[0]//2, polls[0]}):
                    error = error_type('external cancellation')
                    with self.subTest(error=error_type.__name__, after=after):
                        with self.assertRaises(error_type) as caught:
                            operation(Callback(after, error))
                        self.assertIs(caught.exception, error)

    def test_callback_cannot_be_swallowed_by_shelling_geometry_validation(self):
        original = chain_module.verify_boundary_shellings
        state = {'inside': False, 'polls': 0}
        def nested(*args, **kwargs):
            state['inside'] = True
            try:
                return original(*args, **kwargs)
            finally:
                state['inside'] = False
        for operation in (
                lambda check: verify_crushing_chain(self.diagram, self.terminal, check=check),
                lambda check: make_crushing_chain(self.diagram, [], shelling=self.shelling, check=check)):
            error = NormalOrbitError('caller exception inside shelling source validation')
            state['polls'] = 0
            def cancel():
                if state['inside']:
                    state['polls'] += 1
                    # First poll is outside the old shelling checker's catch;
                    # the second is inside _prepare and its malformed-data catch.
                    if state['polls'] == 2:
                        raise error
            with patch.object(chain_module, 'verify_boundary_shellings', nested):
                with self.assertRaises(NormalOrbitError) as caught:
                    operation(cancel)
            self.assertIs(caught.exception, error)


if __name__ == '__main__':
    unittest.main()
