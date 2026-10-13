"""Cheap factor priority, selective nontriviality proofs and checked reduction."""
from copy import deepcopy
import unittest
from unittest.mock import patch

from fastunknot.compressed_braid import recognize, verify, InvalidCertificate
from fastunknot.compressed_braid import cube, exceptional
from compressed_braid_research.families import sleeve
from test_compressed_braid_fallback import grammar, join, UNKNOT, KNOT


class AdaptiveForestTests(unittest.TestCase):
    def test_elementary_reduction_avoids_cube(self):
        data = grammar(4, UNKNOT)
        with patch.object(cube, 'produce', side_effect=AssertionError):
            result = recognize(data, fallback_max_generators=0)
        self.assertEqual(result['status'], 'UNKNOT')
        self.assertEqual(result['resources']['cube_generators'], 0)
        child = result['certificate']['leaves'][0]['certificate']
        self.assertEqual(child['version'], 'exceptional-reduction-v1')
        self.assertEqual(child['reduction']['final_strands'], 3)
        self.assertEqual(verify(data, result['certificate'], fallback_max_generators=0), 'UNKNOT')

    def test_stalled_reduction_retains_complete_cube(self):
        data = grammar(4, KNOT)
        result = recognize(data)
        self.assertEqual(result['status'], 'KNOTTED')
        self.assertGreater(result['resources']['cube_generators'], 0)
        self.assertEqual(result['certificate']['leaves'][0]['certificate']['version'], 'exceptional-cube-f2-v1')
        self.assertEqual(verify(data, result['certificate']), 'KNOTTED')

    def test_shorter_wider_residual_has_bound_cube_proof(self):
        data = grammar(4, KNOT+[1,-1])
        result = recognize(data)
        child = result['certificate']['leaves'][0]['certificate']
        self.assertEqual(child['version'], 'exceptional-reduction-v1')
        self.assertEqual(child['reduction']['final_strands'], 4)
        self.assertEqual(child['terminal']['word'], KNOT)
        self.assertEqual(sum(child['terminal']['homology']), 27)
        self.assertEqual(verify(data, result['certificate']), 'KNOTTED')

    def test_later_finite_obstruction_precedes_any_cube(self):
        data = join(grammar(4, UNKNOT), grammar(2, [1]*3))
        with patch.object(cube, 'produce', side_effect=AssertionError), \
             patch.object(exceptional, 'produce', side_effect=AssertionError):
            result = recognize(data, fallback_max_generators=0, max_nodes=0)
        self.assertEqual(result['status'], 'KNOTTED')
        self.assertEqual(result['factor_order'], [1])
        self.assertEqual(result['resources']['arenas'], 0)
        cert = result['certificate']
        self.assertEqual(cert['phase'], 'knotted-factor')
        self.assertEqual(cert['factor_index'], 1)
        self.assertEqual(len(cert['leaves']), 1)
        self.assertEqual(verify(data, cert, fallback_max_generators=0, max_nodes=0), 'KNOTTED')

    def test_compressed_negative_precedes_wider_cube(self):
        data = join(grammar(4, UNKNOT), sleeve(16, negative=True))
        with patch.object(cube, 'produce', side_effect=AssertionError):
            result = recognize(data, fallback_max_generators=0)
        self.assertEqual(result['status'], 'KNOTTED')
        self.assertEqual(result['factor_order'], [1])
        self.assertEqual(result['resources']['cube_generators'], 0)
        self.assertEqual(verify(data, result['certificate']), 'KNOTTED')

    def test_selected_factor_cannot_prove_unknot_or_change_interval(self):
        data = join(grammar(4, UNKNOT), grammar(2, [1]*3))
        cert = recognize(data)['certificate']
        for field, value in (('status', 'UNKNOT'), ('factor_index', 0),
                             ('factor_index', True), ('phase', 'split'),
                             ('version', 'compressed-singleton-forest-v2')):
            bad = deepcopy(cert)
            bad[field] = value
            with self.assertRaises(InvalidCertificate):
                verify(data, bad)
        positive = recognize(grammar(4, UNKNOT))['certificate']
        positive.update(phase='knotted-factor', factor_index=0, status='KNOTTED')
        with self.assertRaises(InvalidCertificate):
            verify(grammar(4, UNKNOT), positive)

    def test_all_trivial_factors_are_still_required_in_original_order(self):
        data = join(grammar(4, UNKNOT), sleeve(2))
        result = recognize(data)
        self.assertEqual(result['factor_order'], [1, 0])
        self.assertEqual([r['low'] for r in result['certificate']['leaves']], [1, 5])
        self.assertEqual(verify(data, result['certificate']), 'UNKNOT')
        bad = deepcopy(result['certificate'])
        bad['leaves'].pop()
        with self.assertRaises(InvalidCertificate):
            verify(data, bad)

    def test_reduction_mutations_and_version_downgrade_fail(self):
        data = grammar(4, UNKNOT)
        cert = recognize(data)['certificate']
        for field, value in (('final_word', [True, 2]), ('final_strands', 4),
                             ('input_length', 1)):
            bad = deepcopy(cert)
            bad['leaves'][0]['certificate']['reduction'][field] = value
            with self.assertRaises(ValueError):
                verify(data, bad)
        bad = deepcopy(cert)
        bad['leaves'][0]['certificate']['terminal']['input']['root'] = 0
        with self.assertRaises(InvalidCertificate):
            verify(data, bad)
        bad = deepcopy(cert)
        bad['version'] = 'compressed-singleton-forest-v2'
        with self.assertRaises(InvalidCertificate):
            verify(data, bad)

    def test_replay_uses_no_reduction_or_rank_discovery(self):
        for word in (UNKNOT, KNOT+[1,-1]):
            data = grammar(4, word)
            cert = recognize(data)['certificate']
            with patch.object(exceptional, 'singleton_reduce', side_effect=AssertionError), \
                 patch.object(cube, 'rank_trace', side_effect=AssertionError):
                self.assertIn(verify(data, cert), ('UNKNOT', 'KNOTTED'))

    def test_legacy_complete_forest_proofs_still_replay(self):
        data = grammar(4, KNOT)
        cert = recognize(data, use_fallback_reduction=False)['certificate']
        cert.update(version='compressed-singleton-forest-v2', phase='split')
        del cert['factor_index']
        self.assertEqual(verify(data, cert), 'KNOTTED')
        data = grammar(2, [1]*3)
        cert = recognize(data)['certificate']
        cert.update(version='compressed-singleton-forest-v1', phase='split')
        del cert['factor_index']
        self.assertEqual(verify(data, cert), 'KNOTTED')

    def test_shared_work_includes_reduction_and_replay(self):
        data = grammar(4, UNKNOT)
        full = recognize(data)
        work = full['resources']['work']
        self.assertEqual(recognize(data, max_work=work)['status'], 'UNKNOT')
        limited = recognize(data, max_work=work-1)
        self.assertEqual(limited['status'], 'INCONCLUSIVE')
        self.assertNotIn('certificate', limited)
        with self.assertRaises(ValueError):
            recognize(data, use_fallback_reduction=1)

    def test_external_valueerror_cancellation_is_not_reclassified(self):
        class Cancelled(ValueError):
            pass
        data = grammar(4, UNKNOT)
        cert = recognize(data)['certificate']
        original = exceptional.verify_singleton_reduction
        def interrupt(strands, word, proof, check):
            def cancel():
                raise Cancelled('external cancellation')
            return original(strands, word, proof, cancel)
        with patch.object(exceptional, 'verify_singleton_reduction', side_effect=interrupt):
            with self.assertRaises(Cancelled):
                verify(data, cert)


if __name__ == '__main__':
    unittest.main()
