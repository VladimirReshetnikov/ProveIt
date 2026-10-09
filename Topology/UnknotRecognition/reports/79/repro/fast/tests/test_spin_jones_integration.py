"""Full-polynomial CLI output and safe one-sided recognition integration."""
import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest

from fastunknot import Diagram, recognize
from fastunknot.__main__ import main
from fastunknot.jones_filter import JONES_BACKENDS, select_jones_filter
from fastunknot.separator_order import verify_width_bounded_order
from fastunknot.spin_jones import spin_jones_exact


OPTIONS = dict(jones_backend='spin-faithful', use_braid=False, use_seifert=False,
               use_reduction=False, use_descending=False, use_factorization=False,
               use_modular=False, use_alexander=False, use_r3=False)


class SpinJonesIntegrationTests(unittest.TestCase):
    def test_nontrivial_polynomial_certifies_knot(self):
        diagram = Diagram.from_pd(Diagram.from_braid(3, [1, -2]*5).pd)
        result = recognize(diagram, **OPTIONS)
        self.assertEqual(result.status, 'KNOTTED')
        self.assertEqual(result.method, 'jones-spin-faithful')
        self.assertFalse(result.evidence['jones_polynomial_identity']['is_one'])
        self.assertTrue(verify_width_bounded_order(
            diagram.pd, result.evidence['separator_order']))
        evidence = result.evidence['jones']
        self.assertIn('scaled_bracket_hex', evidence)
        self.assertNotEqual(evidence['scaled_bracket_hex'],
                            evidence['unknot_scaled_bracket_hex'])
        json.dumps(result.evidence)

    def test_identity_requires_the_independent_fallback(self):
        diagram = Diagram.from_pd(Diagram.from_braid(2, [1]).pd)
        result = recognize(diagram, **OPTIONS)
        self.assertEqual(result.status, 'UNKNOT')
        self.assertEqual(result.evidence['jones'], 'inconclusive')
        self.assertTrue(result.evidence['jones_polynomial_identity']['is_one'])
        self.assertIn('khovanov', result.evidence)
        self.assertNotEqual(result.method, 'jones-spin-faithful')

    def test_cap_preserves_order_but_publishes_no_identity(self):
        diagram = Diagram.from_pd(Diagram.from_braid(2, [1, -1, 1]).pd)
        result = recognize(diagram, jones_max_transitions=1, **OPTIONS)
        self.assertEqual(result.status, 'UNKNOT')
        self.assertIn('skipped:', result.evidence['jones'])
        self.assertNotIn('jones_polynomial_identity', result.evidence)
        self.assertTrue(verify_width_bounded_order(
            diagram.pd, result.evidence['separator_order']))
        self.assertIn('khovanov', result.evidence)

    def test_cli_outputs_full_polynomial_and_censored_status(self):
        self.assertIn('spin-faithful', JONES_BACKENDS)
        self.assertEqual(select_jones_filter('spin-faithful')[1], 'jones-spin-faithful')
        diagram = Diagram.from_braid(2, [1, 1, 1])
        expected = spin_jones_exact(diagram, include_polynomial=True)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)/'trefoil.json'
            path.write_text(json.dumps({'pd': diagram.pd}))
            output = io.StringIO()
            with contextlib.redirect_stdout(output):
                code = main(['jones', str(path), '--backend', 'spin-faithful'])
            self.assertEqual(code, 0)
            result = json.loads(output.getvalue())
            self.assertEqual(result['verdict'], 'KNOTTED')
            self.assertEqual(result['jones_polynomial'], expected['jones_polynomial'])
            self.assertFalse(result['polynomial_identity']['is_one'])
            output = io.StringIO()
            with contextlib.redirect_stdout(output):
                code = main(['jones', str(path), '--backend', 'spin-faithful',
                             '--max-states', '0'])
            self.assertEqual(code, 3)
            result = json.loads(output.getvalue())
            self.assertEqual(result['verdict'], 'INCONCLUSIVE')
            self.assertNotIn('polynomial_identity', result)


if __name__ == '__main__':
    unittest.main()
