"""Positive replay, deliberate certificate corruption and resource propagation."""
import copy
import json
import unittest
from unittest.mock import patch

from fastunknot import Diagram
from fastunknot.boundary_tait import BoundaryTait, coloring
from fastunknot.geometry import ScanLimit
from fastunknot.modular_response import ModularTerminalKernel
from fastunknot.modular_shadow import ModularClosureShadow, modular_shadow_khovanov_decide
from fastunknot.modular_verify import (ModularVerificationError, replay_modular_shadow,
                                      verify_modular_shadow)
from fastunknot.scan_fast import FastScan
from fastunknot.shadow_scan import ClosureShadow


class ModularReplayTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.examples = []
        for strands, word in ((2, [1, 1, 1]), (3, [1, -2] * 2), (3, [1, 2] * 5)):
            diagram = Diagram.from_braid(strands, word)
            result = modular_shadow_khovanov_decide(diagram.pd, order=list(range(len(word))),
                shadow_max_work=None, primes=(3, 5, 7, 11, 13))
            assert result['method'] == 'marked-residue-four-modular'
            cls.examples.append((diagram, result))

    def test_replays_json_round_trips_and_full_prefix_components(self):
        for diagram, result in self.examples:
            before = copy.deepcopy(result)
            output = replay_modular_shadow(diagram.pd, json.loads(json.dumps(result)))
            self.assertTrue(output['verified'])
            self.assertGreaterEqual(output['verified_weighted_lower_bound'], 2)
            for record in output['components']:
                self.assertLessEqual(record['verified_norm'], record['exact_norm'])
            self.assertTrue(verify_modular_shadow(diagram, result))
            self.assertEqual(result, before)
        self.assertGreater(self.examples[-1][1]['stage'], 0)
        self.assertGreater(len(self.examples[-1][1]['components'][0]['objects']), 1)

    def test_replay_does_not_call_new_modular_arithmetic(self):
        diagram, result = self.examples[-1]
        with patch.object(ModularClosureShadow, 'evaluate', side_effect=AssertionError('new observer')):
            with patch.object(ModularTerminalKernel, 'build', side_effect=AssertionError('new kernel')):
                with patch('fastunknot.modular_lattice.minimum_l1_lift',
                           side_effect=AssertionError('new lattice minimizer')):
                    self.assertTrue(verify_modular_shadow(diagram.pd, result))

    def test_source_order_stage_and_mark_must_match(self):
        diagram, result = self.examples[0]
        unknot = Diagram.from_braid(2, [1, 1, -1])
        self.assertFalse(verify_modular_shadow(unknot.pd, result))
        for source in (None, (), ((0, 1, 0, 1),), ((0, 0, 0, 0),), ((0, True, 0, True),)):
            self.assertFalse(verify_modular_shadow(source, result))
        for field, value in (('status', 'UNKNOT'), ('method', 'closed-rank'), ('crossings', 4),
                             ('crossings', True), ('stage', 3), ('stage', -1), ('stage', False),
                             ('order', [0, 0, 2]), ('order', [0, 1]), ('marked_label', -1),
                             ('reduced_rank_lower_bound_capped', 1)):
            tampered = copy.deepcopy(result)
            tampered[field] = value
            self.assertFalse(verify_modular_shadow(diagram.pd, tampered), (field, value))
        self.assertFalse(verify_modular_shadow(diagram.pd, None))

    def test_prime_product_and_observation_metadata_are_checked(self):
        diagram, result = self.examples[1]  # two auxiliary primes are needed here.
        self.assertEqual(result['modular_observation']['primes'], [3, 5])
        for field, value in (('primes', [3, 3]), ('primes', [3, 9]), ('primes', [2, 5]),
                             ('primes', [3, True]), ('primes', []), ('modulus', 3),
                             ('stage', 1), ('observed_components', 2),
                             ('total_components', 2), ('obstruction', False),
                             ('threshold_exact', False)):
            tampered = copy.deepcopy(result)
            tampered['modular_observation'][field] = value
            self.assertFalse(verify_modular_shadow(diagram.pd, tampered), (field, value))
        tampered = copy.deepcopy(result)
        tampered['components'][0]['modulus'] = 3
        self.assertFalse(verify_modular_shadow(diagram.pd, tampered))

    def test_partial_duplicate_and_unknown_components_are_rejected(self):
        diagram, result = self.examples[-1]
        partial = copy.deepcopy(result)
        partial['components'][0]['objects'].pop()
        partial['components'][0]['relative_q'].pop()
        self.assertFalse(verify_modular_shadow(diagram.pd, partial))
        duplicate = copy.deepcopy(result)
        duplicate['components'].append(copy.deepcopy(duplicate['components'][0]))
        duplicate['modular_observation']['observed_components'] += 1
        self.assertFalse(verify_modular_shadow(diagram.pd, duplicate))
        for objects in ([], [10**6], [True], list(reversed(result['components'][0]['objects']))):
            tampered = copy.deepcopy(result)
            tampered['components'][0]['objects'] = objects
            self.assertFalse(verify_modular_shadow(diagram.pd, tampered))
        empty = copy.deepcopy(result)
        empty['components'] = []
        empty['modular_observation']['observed_components'] = 0
        self.assertFalse(verify_modular_shadow(diagram.pd, empty))

    def test_residues_quantum_phases_and_scalar_metadata_are_checked(self):
        diagram, result = self.examples[-1]
        for field, value in (('residues', [0, 0, 0, 0]), ('residues', [3, 0, 2, 0]),
                             ('residues', [True, 0, 2, 0]), ('residues', [1, 2]),
                             ('exact_euler', 1), ('coordinate_bound', 0),
                             ('multiplicity', 0), ('multiplicity', 2), ('norm', 0),
                             ('minimum_lift', [0, 0, 0, 0])):
            tampered = copy.deepcopy(result)
            tampered['components'][0][field] = value
            self.assertFalse(verify_modular_shadow(diagram.pd, tampered), (field, value))
        for amount in (1, 4):
            tampered = copy.deepcopy(result)
            tampered['components'][0]['relative_q'][1] += amount
            self.assertFalse(verify_modular_shadow(diagram.pd, tampered))
        uniform = copy.deepcopy(result)
        uniform['components'][0]['relative_q'] = [q + 4 for q in uniform['components'][0]['relative_q']]
        self.assertFalse(verify_modular_shadow(diagram.pd, uniform))
        for field in ('euler_characteristics', 'multiplicities_capped'):
            tampered = copy.deepcopy(result)
            tampered[field][0] += 1
            self.assertFalse(verify_modular_shadow(diagram.pd, tampered))
        extra = copy.deepcopy(result)
        extra['components'][0]['phase'] = 0
        self.assertFalse(verify_modular_shadow(diagram.pd, extra))

    def test_feasible_nonminimal_lift_is_rejected_even_below_the_exact_norm(self):
        diagram, result = self.examples[-1]
        tampered = copy.deepcopy(result)
        # This is the exact vector itself and has the right residues and sum,
        # but its norm 4 is larger than the modular lattice minimum 2.
        tampered['components'][0]['minimum_lift'] = [-2, 0, 2, 0]
        tampered['components'][0]['norm'] = 4
        with self.assertRaisesRegex(ModularVerificationError, 'minimum possible norm'):
            replay_modular_shadow(diagram.pd, tampered)

    def test_resource_limits_propagate_and_are_shared_with_integer_observer(self):
        diagram, result = self.examples[-1]
        before = copy.deepcopy(result)
        for options in ({'seconds': 0}, {'max_objects': 0}, {'max_objects': 1}):
            with self.assertRaises(ScanLimit):
                verify_modular_shadow(diagram.pd, result, **options)
        for options in ({'seconds': -1}, {'seconds': float('inf')}, {'seconds': float('nan')},
                        {'seconds': True}, {'max_objects': -1}, {'max_objects': True}):
            with self.assertRaises(ModularVerificationError):
                replay_modular_shadow(diagram.pd, result, **options)
        original = ClosureShadow.evaluate

        def expire(engine, *args, **kwargs):
            self.assertIsNotNone(engine.deadline)
            engine.deadline = 0
            return original(engine, *args, **kwargs)

        with patch.object(ClosureShadow, 'evaluate', expire):
            with self.assertRaises(ScanLimit):
                verify_modular_shadow(diagram.pd, result, seconds=5)
        self.assertEqual(result, before)

    def test_shapes_only_change_caching_and_replay_preserves_object_identity(self):
        diagram, _ = self.examples[-1]
        for enabled in (False, True):
            result = modular_shadow_khovanov_decide(diagram.pd,
                order=list(range(diagram.crossings)), shape_cache=enabled,
                shadow_max_work=None, primes=(3, 5, 7))
            self.assertTrue(verify_modular_shadow(diagram.pd, result))

    def test_exact_terminal_count_and_frontier_query_dimension(self):
        nonempty = queries = empty = 0
        for strands, word in ((2, [1] * 7), (3, [1, -2] * 4), (3, [1, 2] * 5)):
            diagram = Diagram.from_braid(strands, word)
            order = list(reversed(range(diagram.crossings)))
            palette = coloring(diagram.pd)
            scan = FastScan(shape_cache=False)
            for stage, index in enumerate(order):
                geometry = BoundaryTait(diagram.pd, order, stage, palette)
                b = len(geometry.labels)
                if b:
                    self.assertEqual(2 * len(geometry.terminals), b)
                    nonempty += 1
                else:
                    self.assertEqual(len(geometry.terminals), 1)
                    empty += 1
                for prime in (3, 5, 101):
                    kernel = ModularTerminalKernel.build(geometry.laplacian,
                                                          geometry.terminals, prime)
                    for matching in set(scan.mid) - {None}:
                        data = geometry.partition(scan.algebra.pairs[matching])
                        q = len(set(data['partition'])) - 1
                        if kernel.nullity <= q:
                            dimension = kernel.nullity + q
                            self.assertLessEqual(dimension, b - 2 if b else 0)
                            queries += 1
                scan.add_crossing(diagram.pd[index])
        self.assertGreater(nonempty, 15)
        self.assertGreater(queries, 100)
        self.assertEqual(empty, 3)


if __name__ == '__main__':
    unittest.main()
