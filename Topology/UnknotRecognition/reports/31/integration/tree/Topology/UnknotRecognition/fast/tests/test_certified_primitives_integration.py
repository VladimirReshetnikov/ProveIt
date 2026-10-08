"""End-to-end semantics of the optional tensor and overlap policies."""
import contextlib
import io
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from fastunknot import Diagram
from fastunknot.__main__ import main
from fastunknot.compressed_search import compressed_certificate
from fastunknot.group_certificate import group_decide, verify_group_certificate
from fastunknot.recognize import recognize
from fastunknot.separator_order import verify_width_bounded_order


ROOT = Path(__file__).resolve().parents[1]
FILTER_OPTIONS = dict(use_braid=False, use_rational=False, use_seifert=False,
                      use_reduction=False, use_descending=False,
                      use_factorization=False, use_modular=False,
                      use_alexander=False, use_r3=False)


class CertifiedPrimitivesIntegrationTests(unittest.TestCase):
    def test_tensor_obstruction_and_identity_fallback(self):
        weaving = Diagram.from_pd(Diagram.from_braid(3, [1, -2]*5).pd)
        result = recognize(weaving, jones_backend='tensor', **FILTER_OPTIONS)
        self.assertEqual((result.status, result.method),
                         ('KNOTTED', 'jones-tensor-exact'))
        self.assertIn('jones_polynomial', result.evidence)
        self.assertTrue(verify_width_bounded_order(
            weaving.pd, result.evidence['separator_order']))
        kink = Diagram.from_pd(Diagram.from_braid(2, [1]).pd)
        result = recognize(kink, jones_backend='tensor', **FILTER_OPTIONS)
        self.assertEqual(result.status, 'UNKNOT')
        self.assertEqual(result.evidence['jones'], 'inconclusive')
        self.assertTrue(result.evidence['jones_polynomial_identity']['is_one'])
        self.assertIn('khovanov', result.evidence)
        capped = recognize(kink, jones_backend='tensor', max_objects=0,
                           **FILTER_OPTIONS)
        self.assertEqual(capped.status, 'UNKNOWN')
        self.assertTrue(capped.evidence['jones_polynomial_identity']['is_one'])

    def test_tensor_resource_decline_does_not_publish_a_polynomial(self):
        d = Diagram.from_pd(Diagram.from_braid(2, [1, 1, 1]).pd)
        result = recognize(d, jones_backend='tensor', jones_max_transitions=0,
                           max_objects=0, **FILTER_OPTIONS)
        self.assertEqual(result.status, 'UNKNOWN')
        self.assertNotIn('jones_polynomial_identity', result.evidence)
        self.assertNotIn('jones_polynomial', result.evidence)

    def test_cli_tensor_full_polynomial_and_resource_decline(self):
        for name, verdict in [('trefoil', 'KNOTTED'),
                              ('hard_unknot_8', 'INCONCLUSIVE')]:
            output = io.StringIO()
            with contextlib.redirect_stdout(output):
                code = main(['jones', str(ROOT/'examples'/(name+'.json')),
                             '--backend', 'tensor'])
            self.assertEqual(code, 0)
            result = json.loads(output.getvalue())
            self.assertEqual(result['verdict'], verdict)
            self.assertIn('jones_polynomial', result)
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            code = main(['jones', str(ROOT/'examples/trefoil.json'),
                         '--backend', 'tensor', '--max-transitions', '0'])
        self.assertEqual(code, 3)
        self.assertNotIn('jones_polynomial', json.loads(output.getvalue()))

    def test_public_group_policy_produces_independently_replayed_certificate(self):
        d = Diagram.from_json(json.loads((ROOT/'examples/hard_unknot_8.json').read_text()))
        result = group_decide(d, seconds=None, compressed_search=True,
                              relator_moves=True, overlap_witness=True)
        self.assertEqual(result['status'], 'UNKNOT')
        self.assertTrue(verify_group_certificate(d, result['certificate']))
        with patch('fastunknot.compressed_search._search', return_value=False) as search:
            self.assertIsNone(compressed_certificate(d, relator_moves=True,
                                                     overlap_witness=True))
        self.assertIs(search.call_args.kwargs['overlap_witness'], True)

    def test_cli_group_flag_enables_its_required_search_options(self):
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            code = main(['recognize', str(ROOT/'examples/hard_unknot_8.json'),
                         '--group-overlap-witness', '--group-seconds', '2',
                         '--no-braid', '--no-seifert', '--no-reduction',
                         '--no-descending', '--no-factor', '--no-alexander',
                         '--no-jones', '--no-r3'])
        self.assertEqual(code, 0)
        result = json.loads(output.getvalue())
        self.assertEqual(result['status'], 'UNKNOT')
        self.assertEqual(result['method'], 'wirtinger-cyclic-group')
        self.assertEqual(result['evidence']['group']['search_backend'], 'compressed-slp')

    def test_policy_validation(self):
        d = Diagram.from_pd([])
        for options in ({'overlap_witness': 1}, {'overlap_witness': True}):
            with self.assertRaises(ValueError):
                compressed_certificate(d, **options)
            with self.assertRaises(ValueError):
                group_decide(d, **options)
        for options in ({'group_overlap_witness': 1},
                        {'group_overlap_witness': True}):
            with self.assertRaises(ValueError):
                recognize(d, **options)


if __name__ == '__main__':
    unittest.main()
