"""Independent polynomial recovery, real adaptive restarts, and safe verdicts."""
import contextlib
import io
import json
from pathlib import Path
import random
import sys
import unittest
from unittest.mock import patch

from fastunknot import Diagram, recognize
from fastunknot.__main__ import main
from fastunknot.faithful_jones import faithful_colors, faithful_potts_exact, reconstruct_jones
from fastunknot.geometry import ScanLimit
from fastunknot.potts_exact import PottsLimit, potts_exact, witness_from_exact
from fastunknot.potts_factorized_exact import factorized_potts_exact
from fastunknot.separator_order import verify_width_bounded_order
from check_potts_independent import evaluate, laurent_jones, times
from test_adaptive_potts import shuffled_grids
from test_shadow_scan import diagrams


def coefficients(result):
    return {degree: int(c, 16) for degree, c in result['jones_polynomial']['coefficients_hex']}


class FaithfulJonesTests(unittest.TestCase):
    def test_identity_shortcut_requires_faithful_base_and_nonzero_normalization(self):
        result = dict(crossing_count=254, q=faithful_colors(254),
                      partition_function=[1 << 20000, -(1 << 19000)],
                      unknot_partition=[1 << 20000, -(1 << 19000)])
        with patch('fastunknot.faithful_jones.multiply',
                   side_effect=AssertionError('identity computed the normalization product')):
            self.assertEqual(reconstruct_jones(result), {0: 1})
        with self.assertRaises(ValueError):
            reconstruct_jones(dict(result, q=6))
        with self.assertRaises(ArithmeticError):
            reconstruct_jones(dict(result, partition_function=[0, 0], unknot_partition=[0, 0]))
        calls = 0

        def stop_on_publication():
            nonlocal calls
            calls += 1
            if calls == 2:
                raise ScanLimit('deadline before identity publication')

        with self.assertRaises(ScanLimit):
            reconstruct_jones(result, check=stop_on_publication)

    def test_independent_full_polynomial_both_shades_and_mirrors(self):
        cases = list(diagrams(35, 2628))
        root = Path(__file__).resolve().parents[1] / 'examples'
        for name in ('conway', 'kinoshita_terasaka', 'hard_unknot_8'):
            d = Diagram.from_json(json.loads((root / (name+'.json')).read_text()))
            cases.append((d, list(range(d.crossings))))
        cases.append((Diagram.from_pd([]), []))
        for d, order in cases:
            for d in (d, d.mirror()):
                expected = {-k: v for k, v in laurent_jones(d).items()}
                for shade in (0, 1):
                    result = faithful_potts_exact(d, order=order, shade=shade,
                                                  include_polynomial=True,
                                                  max_states=None, max_transitions=None)
                    self.assertEqual(coefficients(result), expected)
                    self.assertEqual(result['polynomial_identity']['is_one'], expected == {0: 1})

    def test_bounded_laurent_recovery_including_extreme_signed_coefficients(self):
        rng = random.Random(2629)
        for n in range(1, 18):
            colors = faithful_colors(n)
            bound = 1 << (2*n)
            cases = [{-2*n: bound}, {2*n: -bound}, {-2*n: bound//2, 2*n: -bound//2}]
            for _ in range(8):
                p = {}
                for _ in range(10):
                    degree = rng.randrange(-2*n, 2*n+1)
                    p[degree] = p.get(degree, 0)+rng.randrange(-(bound//32), bound//32+1)
                cases.append({k: v for k, v in p.items() if v})
            for p in cases:
                # Oracle uses x=A^4; public reconstruction returns t=A^-4.
                scalar = evaluate(p, colors)
                normalization = evaluate({-3: 1, 2: -2}, colors)
                result = dict(crossing_count=n, q=colors,
                              partition_function=list(times(scalar, normalization, colors)),
                              unknot_partition=list(normalization))
                self.assertEqual(reconstruct_jones(result), {-k: v for k, v in p.items()})
        with self.assertRaises(ValueError):
            reconstruct_jones(dict(crossing_count=1, q=6))

    def test_real_restart_and_shared_transition_allowance(self):
        d, order = list(shuffled_grids())[1]
        result = faithful_potts_exact(d, order=order, include_polynomial=True)
        self.assertEqual(result['ordering_policy']['mode'], 'certified-restart')
        self.assertTrue(verify_width_bounded_order(d.pd, result['order_certificate']))
        self.assertEqual(coefficients(result), {0: 1})
        exact = faithful_potts_exact(d, order=order, max_transitions=result['transitions'])
        self.assertEqual(exact['partition_function'], result['partition_function'])
        stats = {}
        with self.assertRaises(PottsLimit) as caught:
            faithful_potts_exact(d, order=order, max_transitions=result['transitions']-1,
                                 statistics=stats)
        self.assertEqual(caught.exception.transitions, result['transitions']-1)
        self.assertNotIn('polynomial_identity', stats)
        self.assertNotIn('partition_function', stats)

    def test_collision_removed_and_polynomial_identity_still_uses_fallback(self):
        d = Diagram.from_pd(Diagram.from_braid(3, [1, -2]*5).pd)
        self.assertFalse(potts_exact(d, colors=5)['differs'])
        self.assertFalse(faithful_potts_exact(d)['polynomial_identity']['is_one'])
        options = dict(jones_backend='potts-faithful', use_braid=False, use_seifert=False,
                       use_reduction=False, use_descending=False, use_factorization=False,
                       use_modular=False, use_alexander=False, use_r3=False)
        knot = recognize(d, **options)
        self.assertEqual(knot.status, 'KNOTTED')
        self.assertEqual(knot.method, 'jones-potts-faithful')
        unknot = recognize(Diagram.from_pd(Diagram.from_braid(2, [1]).pd), **options)
        self.assertEqual(unknot.status, 'UNKNOT')
        self.assertEqual(unknot.evidence['jones'], 'inconclusive')
        self.assertTrue(unknot.evidence['jones_polynomial_identity']['is_one'])
        self.assertIn('khovanov', unknot.evidence)

    def test_large_colors_have_json_safe_witness_without_global_changes(self):
        get_limit = getattr(sys, 'get_int_max_str_digits', lambda: None)
        before = get_limit()
        d, q = Diagram.from_braid(2, [1, 1, 1]), (1 << 20_000)+2
        for evaluator in (potts_exact, factorized_potts_exact):
            result = evaluator(d, colors=q)
            witness = witness_from_exact(result)
            encoded = json.loads(json.dumps(witness))
            self.assertEqual(int(encoded['q_hex'], 16), q)
            self.assertNotIn('q', encoded)
            self.assertEqual(encoded['ring'], 'Z[x]/(x^2-(q-2)*x+1)')
        self.assertEqual(get_limit(), before)

    def test_validation_local_caps_and_global_cancellation(self):
        d = Diagram.from_braid(2, [1, 1, 1])
        for options in ({'max_states': -1}, {'max_transitions': True},
                        {'include_polynomial': 1}, {'shade': True}, {'order': [0]}):
            with self.assertRaises(ValueError):
                faithful_potts_exact(d, **options)
        for n in (True, -1, 1.5):
            with self.assertRaises(ValueError):
                faithful_colors(n)
        for options in ({'max_states': 0}, {'max_transitions': 0}):
            stats = {}
            with patch('fastunknot.faithful_jones.faithful_colors',
                       side_effect=AssertionError('zero budget allocated the large base')):
                with self.assertRaises(PottsLimit):
                    faithful_potts_exact(d, statistics=stats, **options)
            self.assertNotIn('polynomial_identity', stats)
        stats = {}
        with patch('fastunknot.faithful_jones.reconstruct_jones',
                   side_effect=ScanLimit('deadline during decoding')):
            with self.assertRaises(ScanLimit):
                faithful_potts_exact(d, include_polynomial=True, statistics=stats)
        self.assertNotIn('polynomial_identity', stats)
        self.assertNotIn('jones_polynomial', stats)
        self.assertEqual(coefficients(faithful_potts_exact(Diagram.from_pd([]), max_states=0,
                                                          include_polynomial=True)), {0: 1})

    def test_cli_full_polynomial_and_resource_limit(self):
        root = Path(__file__).resolve().parents[1] / 'examples'
        for name, expected in [('trefoil', 'KNOTTED'), ('hard_unknot_8', 'INCONCLUSIVE')]:
            stream = io.StringIO()
            with contextlib.redirect_stdout(stream):
                code = main(['jones', str(root/(name+'.json')), '--backend', 'potts-faithful'])
            self.assertEqual(code, 0)
            result = json.loads(stream.getvalue())
            self.assertEqual(result['verdict'], expected)
            self.assertEqual(result['polynomial_identity']['is_one'], expected == 'INCONCLUSIVE')
            self.assertIn('jones_polynomial', result)
        stream = io.StringIO()
        with contextlib.redirect_stdout(stream):
            code = main(['jones', str(root/'trefoil.json'), '--backend', 'potts-faithful',
                         '--max-transitions', '0'])
        self.assertEqual(code, 3)
        self.assertNotIn('polynomial_identity', json.loads(stream.getvalue()))


if __name__ == '__main__':
    unittest.main()
