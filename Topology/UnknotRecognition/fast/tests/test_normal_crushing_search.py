"""Native recognition, shared allowances, and hostile global certificates."""
from copy import deepcopy
from itertools import product
from random import Random
import unittest
from unittest.mock import patch

from fastunknot.diagram import Diagram
from fastunknot.normal_crushing_chain import make_crushing_chain, verify_crushing_chain
from fastunknot.normal_crushing_search import recognize_by_crushing, verify_crushing_recognition
from fastunknot import normal_crushing_search as search_module
from fastunknot.normal_sector import SearchLimit, _source_hash, build_sector_kernel, sector_rays
from fastunknot.normal_sector_verify import verify_sector_exhaustion
from fastunknot.normal_surface_geometry import NormalOrbitError, _coordinates


# A real source-extreme positive ray on the canonical shelled unknot source.
# Its nonterminal crush selects a one-tetrahedron solid torus.
REDUCTION_RAY = [
    [1, 0, 0, 1, 0, 0, 1], [1, 1, 1, 1, 0, 0, 0],
    [0, 1, 1, 0, 0, 0, 1], [1, 0, 0, 1, 0, 0, 1],
    [0, 1, 1, 0, 0, 0, 1],
]


def reduction_first(count, order, check):
    """Reorder only the first source's sectors, preserving actual native rays."""
    if count == 5:
        yield (2,)*5
        yield from (a for a in product(range(3), repeat=count) if a != (2,)*5)
    else:
        yield from product(range(3), repeat=count)


class CrushingRecognitionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.diagram = Diagram.from_pd([])
        cls.result = recognize_by_crushing(cls.diagram, sector_order='canonical')
        cls.proof = cls.result['certificate']
        cls.partial = make_crushing_chain(cls.diagram, [REDUCTION_RAY],
                                          shelling=cls.proof['chain']['shelling'])
        cls.one_tet = cls.partial['triangulation']
        cls.false_negative = dict(schema='diagram-crushing-recognition-v1',
            status='KNOTTED', chain=cls.partial, exhaustion=[])
        # Exhaust all three one-tetrahedron sectors honestly, then falsely
        # claim their Euler values are nonpositive. The last is in fact +1.
        cls.actual_euler = []
        for q in range(3):
            kernel = build_sector_kernel(cls.one_tet, [[0, q]])
            entries = []
            for rows in sector_rays(kernel, phase='quadrilateral'):
                chi = _coordinates(kernel.prepared, rows, lambda: None)['euler_characteristic']
                cls.actual_euler.append(chi)
                entries.append(dict(quadrilaterals=[rows[0][4+q]], euler_characteristic=0))
            cls.false_negative['exhaustion'].append(dict(schema='normal-sector-exhaustion-v1',
                source_sha256=_source_hash(cls.one_tet), allowed_types=[[0, q]],
                phase='quadrilateral', status='NO_POSITIVE_EULER', rays=entries))

    def test_crossing_free_diagram_is_recognized_by_authenticated_native_crushing(self):
        self.assertEqual(self.result['status'], 'UNKNOT')
        self.assertEqual(self.result['stats'], dict(initial_tetrahedra=20,
            shelled_tetrahedra=5, sectors_attempted=1, bases_attempted=1,
            rays_examined=1, positive_euler_rays=1, crushing_steps=1, stages=1,
            matching_support_checks=1, matching_support_reductions=0, forced_zero_types=0,
            sector_restarts=0, sector_quantum_exhaustions=0, max_cached_sector_jobs=1))
        self.assertEqual(self.proof['schema'], 'diagram-crushing-recognition-v1')
        self.assertEqual(self.proof['exhaustion'], [])
        self.assertIsNone(self.proof['chain']['triangulation'])
        self.assertTrue(verify_crushing_recognition(self.diagram, self.proof))
        result = recognize_by_crushing(self.diagram, max_sectors=None,
                                      max_bases=None, max_crushes=None, sector_order='canonical')
        self.assertEqual(result['certificate'], self.proof)
        exact = recognize_by_crushing(self.diagram, max_sectors=1,
                                     max_bases=1, max_crushes=1, sector_order='canonical')
        self.assertEqual(exact['certificate'], self.proof)
        diversified = recognize_by_crushing(self.diagram)
        self.assertEqual(diversified['status'], 'UNKNOT')
        self.assertEqual(diversified['stats']['sectors_attempted'], 2)
        self.assertEqual(diversified['stats']['bases_attempted'], 2)
        self.assertEqual(diversified['stats']['crushing_steps'], 2)
        self.assertTrue(verify_crushing_recognition(self.diagram, diversified['certificate']))

    def test_both_orders_cover_every_sector_once_and_diversification_is_deterministic(self):
        for count in range(6):
            canonical = list(product(range(3), repeat=count))
            for order in ('canonical', 'diversified'):
                actual = list(search_module._sector_assignments(count, order, lambda: None))
                self.assertEqual(len(actual), 3**count)
                self.assertEqual(sorted(actual), canonical)
                self.assertEqual(actual, list(search_module._sector_assignments(
                    count, order, lambda: None)))
                if order == 'canonical':
                    self.assertEqual(actual, canonical)
        random = Random(37)
        expected = tuple(random.randrange(3) for _ in range(48))
        self.assertEqual(next(search_module._sector_assignments(48, 'diversified', lambda: None)),
                         expected)
        for order in (None, False, '', 'random'):
            with self.assertRaises(ValueError):
                recognize_by_crushing(self.diagram, sector_order=order)

    def test_zero_caps_return_inconclusive_with_only_a_partial_source_chain(self):
        for name in ('max_sectors', 'max_bases', 'max_crushes'):
            with self.subTest(cap=name):
                result = recognize_by_crushing(self.diagram, **{name: 0})
                self.assertEqual(result['status'], 'INCONCLUSIVE')
                self.assertNotIn('certificate', result)
                self.assertEqual(result['partial_chain']['status'], 'REDUCED')
                self.assertEqual(result['partial_chain']['steps'], [])
                self.assertTrue(verify_crushing_chain(self.diagram, result['partial_chain']))
        for name in ('max_sectors', 'max_bases', 'max_crushes'):
            for value in (True, -1, 0.5, '1'):
                with self.subTest(cap=name, value=value), self.assertRaises(ValueError):
                    recognize_by_crushing(self.diagram, **{name: value})

    def test_caps_are_shared_across_real_strictly_smaller_sources(self):
        # Different first-sector order selects three genuine positive Q rays.
        # No geometry, enumeration or verification is stubbed out.
        with patch.object(search_module, '_sector_assignments', reduction_first):
            full = recognize_by_crushing(self.diagram)
            self.assertEqual(full['status'], 'UNKNOT')
            self.assertEqual(full['stats']['sectors_attempted'], 3)
            self.assertEqual(full['stats']['bases_attempted'], 3)
            self.assertEqual(full['stats']['crushing_steps'], 3)
            self.assertEqual([None if s['successor'] is None else
                              len(s['successor']['tetrahedra'])
                              for s in full['certificate']['chain']['steps']], [4, 3, None])
            for name in ('max_sectors', 'max_bases', 'max_crushes'):
                with self.subTest(cap=name):
                    result = recognize_by_crushing(self.diagram, **{name: 1})
                    self.assertEqual(result['status'], 'INCONCLUSIVE')
                    self.assertEqual(result['stats']['crushing_steps'], 1)
                    self.assertEqual(len(result['partial_chain']['triangulation']['tetrahedra']), 4)
                    self.assertEqual(result['stats'][{'max_sectors': 'sectors_attempted',
                        'max_bases': 'bases_attempted', 'max_crushes': 'crushing_steps'}[name]], 1)
                    self.assertTrue(verify_crushing_chain(self.diagram, result['partial_chain']))
        self.assertTrue(verify_crushing_recognition(self.diagram, full['certificate']))

    def test_real_complete_negative_sector_transcript_cannot_hide_positive_euler(self):
        self.assertEqual(self.actual_euler, [0, 0, 1])
        self.assertTrue(verify_crushing_chain(self.diagram, self.partial))
        self.assertFalse(verify_crushing_recognition(self.diagram, self.false_negative))
        for mutation in ('remove_ray', 'restore_positive', 'wrong_source', 'wrong_phase'):
            proof = deepcopy(self.false_negative)
            packet = proof['exhaustion'][-1]
            if mutation == 'remove_ray':
                packet['rays'] = []
            elif mutation == 'restore_positive':
                packet['rays'][0]['euler_characteristic'] = 1
            elif mutation == 'wrong_source':
                packet['source_sha256'] = '0'*64
            else:
                packet['phase'] = 'standard'
            self.assertFalse(verify_crushing_recognition(self.diagram, proof), mutation)

    def test_source_proven_matching_pruning_preserves_native_crushing(self):
        # This full sector of the authenticated trefoil exterior has matching
        # nullity 13; source equations force 40 of its 48 Q coordinates zero.
        # Only the traversal order changes. All algebra and geometry remain
        # native and the resulting partial chain must replay independently.
        diagram = Diagram.from_braid(2, [1, 1, 1])
        result = recognize_by_crushing(diagram, max_sectors=1, max_bases=1)
        self.assertEqual(result['status'], 'INCONCLUSIVE')
        self.assertNotIn('certificate', result)
        self.assertEqual(result['stats']['matching_support_reductions'], 1)
        self.assertEqual(result['stats']['forced_zero_types'], 40)
        self.assertEqual(result['stats']['bases_attempted'], 1)
        self.assertEqual(result['stats']['crushing_steps'], 1)
        self.assertLess(len(result['partial_chain']['triangulation']['tetrahedra']), 48)
        self.assertTrue(verify_crushing_chain(diagram, result['partial_chain']))

    def test_negative_global_coverage_requires_every_full_sector_once_in_order(self):
        # Isolate the global coverage gate; real dense replay rejects this
        # forged negative above. This mock provides no recognition evidence.
        with patch.object(search_module, 'verify_sector_exhaustion', return_value=True) as replay:
            self.assertTrue(verify_crushing_recognition(self.diagram, self.false_negative))
            self.assertEqual(replay.call_count, 3)
            for mutation in ('missing', 'duplicate', 'reordered', 'partial', 'extra', 'bool_type'):
                proof = deepcopy(self.false_negative)
                packets = proof['exhaustion']
                if mutation == 'missing':
                    packets.pop()
                elif mutation == 'duplicate':
                    packets[-1] = deepcopy(packets[0])
                elif mutation == 'reordered':
                    packets.reverse()
                elif mutation == 'partial':
                    packets[0]['allowed_types'] = []
                elif mutation == 'extra':
                    packets.append(deepcopy(packets[0]))
                else:
                    packets[0]['allowed_types'][0][1] = False
                self.assertFalse(verify_crushing_recognition(self.diagram, proof), mutation)

    def test_verifier_rejects_modified_chain_and_malformed_top_level_packets(self):
        for proof in (None, [], {}, dict(self.proof, extra=True)):
            self.assertFalse(verify_crushing_recognition(self.diagram, proof))
        for key in self.proof:
            proof = deepcopy(self.proof)
            del proof[key]
            self.assertFalse(verify_crushing_recognition(self.diagram, proof))
        for mutation in ('steps', 'source', 'shelling', 'status', 'exhaustion', 'terminal_knotted'):
            proof = deepcopy(self.proof)
            if mutation == 'steps':
                proof['chain']['steps'] = []
            elif mutation == 'source':
                proof['chain']['source_triangulation']['tetrahedra'].pop()
            elif mutation == 'shelling':
                proof['chain']['shelling']['moves'].pop()
            elif mutation == 'status':
                proof['status'] = 'INCONCLUSIVE'
            elif mutation == 'exhaustion':
                proof['exhaustion'] = [None]
            else:
                proof['status'] = 'KNOTTED'
            self.assertFalse(verify_crushing_recognition(self.diagram, proof), mutation)
        self.assertFalse(verify_crushing_recognition(Diagram.from_braid(2, [1, 1, 1]), self.proof))

    def test_forced_zero_claims_are_replayed_without_weakening_global_coverage(self):
        proof = deepcopy(self.false_negative)
        packet = proof['exhaustion'][0]
        packet['matching_support_certificate'] = dict(
            schema='normal-sector-matching-support-v1', source_sha256=packet['source_sha256'],
            allowed_types=deepcopy(packet['allowed_types']), steps=[dict(
                row_combination=[[0, 1, 1]], forced_indices=[0])])
        # The actual first sector has a nonzero chi=0 Q ray, so an assertion
        # that its only type is forced zero must fail independent replay.
        self.assertFalse(verify_sector_exhaustion(self.one_tet, packet))
        with patch.object(search_module, 'verify_sector_exhaustion',
                          wraps=verify_sector_exhaustion) as replay:
            self.assertFalse(verify_crushing_recognition(self.diagram, proof))
            self.assertEqual(replay.call_count, 1)
        # Isolate the coverage gate again: even a hypothetically accepted
        # all-forced-zero proof leaves the full maximal sector in the packet.
        with patch.object(search_module, 'verify_sector_exhaustion', return_value=True):
            self.assertTrue(verify_crushing_recognition(self.diagram, proof))
            omitted = deepcopy(proof)
            omitted['exhaustion'][0]['allowed_types'] = []
            self.assertFalse(verify_crushing_recognition(self.diagram, omitted))
            omitted = deepcopy(proof)
            omitted['exhaustion'].pop(0)
            self.assertFalse(verify_crushing_recognition(self.diagram, omitted))
            extra = deepcopy(proof)
            extra['exhaustion'][0]['q_support_certificate'] = {}
            self.assertFalse(verify_crushing_recognition(self.diagram, extra))

    def test_replay_uses_no_producer_or_discovery_routines(self):
        with patch('fastunknot.diagram_exterior.diagram_exterior', side_effect=AssertionError), \
             patch('fastunknot.boundary_shellings.shell_boundary', side_effect=AssertionError), \
             patch('fastunknot.normal_crushing.crush_normal_ray', side_effect=AssertionError), \
             patch('fastunknot.normal_crushing_chain.make_crushing_chain', side_effect=AssertionError), \
             patch('fastunknot.normal_sector.build_sector_kernel', side_effect=AssertionError), \
             patch('fastunknot.normal_sector.sector_rays', side_effect=AssertionError), \
             patch('fastunknot.sector_matching_support.matching_support', side_effect=AssertionError), \
             patch.object(search_module, 'recognize_by_crushing', side_effect=AssertionError):
            self.assertTrue(verify_crushing_recognition(self.diagram, self.proof))
            self.assertFalse(verify_crushing_recognition(self.diagram, self.false_negative))

    def test_missing_producer_rays_fail_independent_global_replay(self):
        observed = []
        def replay(diagram, proof, *, check):
            observed.append(proof)
            # Diversified traversal still serializes the complete negative
            # proof in canonical order. Genuine replay then catches the lie.
            self.assertEqual([p['allowed_types'] for p in proof['exhaustion']],
                [[[t, q] for t, q in enumerate(a)] for a in product(range(3), repeat=5)])
            return verify_crushing_recognition(diagram, proof, check=check)
        with patch('fastunknot.normal_sector.sector_rays', return_value=iter(())), \
             patch.object(search_module, 'verify_crushing_recognition', replay):
            with self.assertRaisesRegex(ArithmeticError, 'recognition replay failed'):
                recognize_by_crushing(self.diagram, max_sectors=None, max_bases=None)
        self.assertEqual(len(observed), 1)

    def test_inputs_and_certificates_are_not_mutated(self):
        before = deepcopy(self.proof)
        self.assertTrue(verify_crushing_recognition(self.diagram, self.proof))
        self.assertEqual(self.proof, before)
        before = deepcopy(self.false_negative)
        self.assertFalse(verify_crushing_recognition(self.diagram, self.false_negative))
        self.assertEqual(self.false_negative, before)

    def test_caller_exceptions_including_search_limits_propagate_from_nested_work(self):
        class Callback:
            def __init__(self, after, error):
                self.after, self.error = after, error
            def __bool__(self):
                return False
            def __call__(self):
                self.after -= 1
                if self.after == 0:
                    raise self.error
        operations = (
            lambda check: recognize_by_crushing(self.diagram, check=check),
            lambda check: verify_crushing_recognition(self.diagram, self.proof, check=check),
            lambda check: verify_crushing_recognition(self.diagram, self.false_negative, check=check),
        )
        for operation in operations:
            polls = [0]
            def count():
                polls[0] += 1
            operation(count)
            for error_type in (ValueError, TypeError, NormalOrbitError, SearchLimit, RuntimeError):
                for after in sorted({1, polls[0]//2, polls[0]}):
                    error = error_type('external cancellation')
                    with self.subTest(operation=operation, error=error_type.__name__, after=after):
                        with self.assertRaises(error_type) as caught:
                            operation(Callback(after, error))
                        self.assertIs(caught.exception, error)


if __name__ == '__main__':
    unittest.main()
