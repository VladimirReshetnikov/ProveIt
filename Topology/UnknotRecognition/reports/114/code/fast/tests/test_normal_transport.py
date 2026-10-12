"""Source binding, independent replay, budget and adverse-verdict tests."""
from copy import deepcopy
import unittest
from unittest.mock import patch

from fastunknot import Diagram
from fastunknot.normal_transport import transport_seed_decide
from fastunknot.normal_transport_verify import verify_transport_disk_certificate


class TransportSourceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.diagram = Diagram.from_braid(2, [1])
        cls.result = transport_seed_decide(cls.diagram, max_work=None)

    def test_positive_requires_source_and_entire_move_chain(self):
        self.assertEqual(self.result['status'], 'UNKNOT')
        proof = self.result['certificate']
        self.assertGreater(len(proof['steps']), 0)
        self.assertTrue(verify_transport_disk_certificate(self.diagram, proof))
        self.assertFalse(verify_transport_disk_certificate(
            Diagram.from_braid(2, [1, 1, 1]), proof))
        for key in proof:
            bad = deepcopy(proof)
            del bad[key]
            self.assertFalse(verify_transport_disk_certificate(self.diagram, bad))
        for field, value in [('schema', 'wrong'), ('input_pd', []),
                             ('source_heights', []), ('steps', []),
                             ('coordinates', []), ('disc_certificate', {})]:
            bad = deepcopy(proof)
            bad[field] = value
            self.assertFalse(verify_transport_disk_certificate(self.diagram, bad))

    def test_no_search_or_producer_is_used_in_replay(self):
        with patch('fastunknot.diagram_exterior.diagram_exterior', side_effect=AssertionError), \
             patch('fastunknot.normal_cocycle.rank_one_cocycle_seed', side_effect=AssertionError), \
             patch('fastunknot.cocycle_transport.transport_cocycle', side_effect=AssertionError), \
             patch('fastunknot.cocycle_transport.descend_cocycle', side_effect=AssertionError), \
             patch('fastunknot.pachner32.pachner_32', side_effect=AssertionError), \
             patch('fastunknot.normal_disk_kernel.normal_compressing_disk_count', side_effect=AssertionError):
            self.assertTrue(verify_transport_disk_certificate(self.diagram,
                                                             self.result['certificate']))

    def test_geometry_and_score_forgery_rejected(self):
        for kind in ('score', 'height', 'coordinate', 'move', 'count', 'bool'):
            bad = deepcopy(self.result['certificate'])
            if kind == 'score': bad['steps'][0]['transport']['euler_jump'] += 1
            elif kind == 'height': bad['steps'][0]['transport']['heights'][0][0] += 1
            elif kind == 'coordinate': bad['coordinates'][0][0] += 1
            elif kind == 'move': bad['steps'][0]['transport']['move']['region'] = []
            elif kind == 'count': bad['disc_certificate']['compressing_disk_components'] = 0
            else: bad['source_heights'][0][0] = True
            self.assertFalse(verify_transport_disk_certificate(self.diagram, bad), kind)

    def test_shelling_zero_move_and_optimized_paths(self):
        for options in ({'shellings': True}, {'optimize': True}, {'max_moves': 0},
                        {'strategy': 'first', 'shellings': True}):
            result = transport_seed_decide(self.diagram, max_work=None, **options)
            self.assertEqual(result['status'], 'UNKNOT')
            self.assertTrue(verify_transport_disk_certificate(self.diagram,
                                                             result['certificate']))
        proof = transport_seed_decide(self.diagram, shellings=True,
                                      max_work=None)['certificate']
        proof['shelling']['moves'].append(proof['shelling']['moves'][0])
        self.assertFalse(verify_transport_disk_certificate(self.diagram, proof))

    def test_negative_search_and_budget_are_inconclusive(self):
        for options in ({}, {'shellings': True}, {'optimize': True}):
            answer = transport_seed_decide(Diagram.from_braid(2, [1, 1, 1]),
                                            max_work=None, **options)
            self.assertEqual(answer['status'], 'INCONCLUSIVE')
            self.assertNotIn('certificate', answer)
        self.assertEqual(transport_seed_decide(self.diagram, max_work=0)['status'],
                         'INCONCLUSIVE')
        work = self.result['work']
        self.assertEqual(transport_seed_decide(self.diagram, max_work=work), self.result)
        self.assertEqual(transport_seed_decide(self.diagram, max_work=work-1)['status'],
                         'INCONCLUSIVE')

    def test_cancellation_and_validation(self):
        def cancel(): raise RuntimeError('cancelled')
        with self.assertRaisesRegex(RuntimeError, 'cancelled'):
            transport_seed_decide(self.diagram, check=cancel)
        with self.assertRaisesRegex(RuntimeError, 'cancelled'):
            verify_transport_disk_certificate(self.diagram, self.result['certificate'],
                                                check=cancel)
        for opts in ({'shellings': 1}, {'optimize': 0}, {'strategy': 'wrong'},
                     {'max_moves': True}, {'max_cycles': -1}, {'max_work': False}):
            with self.assertRaises(ValueError): transport_seed_decide(self.diagram, **opts)

    def test_delayed_callback_exceptions_keep_their_identity(self):
        from fastunknot.normal_cocycle import CocycleLimit
        from fastunknot.normal_surface_geometry import NormalOrbitError

        proof = transport_seed_decide(self.diagram, max_moves=0,
                                      max_work=None)['certificate']
        polls = [0]

        def count():
            polls[0] += 1

        self.assertTrue(verify_transport_disk_certificate(self.diagram, proof,
                                                          check=count))
        locations = sorted({1, 31, polls[0]//2, polls[0]})
        for error_type in (ValueError, TypeError, KeyError, IndexError,
                           NormalOrbitError, CocycleLimit, RuntimeError):
            for location in locations:
                error = error_type('caller cancellation')
                remaining = [location]

                def cancel():
                    remaining[0] -= 1
                    if remaining[0] == 0:
                        raise error

                with self.subTest(error=error_type.__name__, poll=location):
                    with self.assertRaises(error_type) as caught:
                        verify_transport_disk_certificate(self.diagram, proof,
                                                          check=cancel)
                    self.assertIs(caught.exception, error)
            error = error_type('caller cancellation')

            def cancel_immediately():
                raise error

            with self.assertRaises(error_type) as caught:
                transport_seed_decide(self.diagram, check=cancel_immediately)
            self.assertIs(caught.exception, error)


if __name__ == '__main__': unittest.main()
