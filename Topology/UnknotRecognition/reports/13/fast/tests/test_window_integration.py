"""Decision soundness and fallback behavior of the opt-in window stage."""
import contextlib
import importlib
import io
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from fastunknot.diagram import Diagram
from fastunknot.recognize import recognize
from fastunknot.__main__ import main

EXAMPLES = Path(__file__).resolve().parents[1] / 'examples'
ONLY_KH = dict(use_reduction=False, use_descending=False, use_factorization=False,
               use_modular=False, use_jones=False, use_alexander=False)


class WindowIntegrationTests(unittest.TestCase):
    def test_automatic_mirror_preserves_original_degree_labels(self):
        from fastunknot.window_bounds import (khovanov_window_auto, state_circle_count,
                                               weighted_binomial_sum)
        from fastunknot.scan import khovanov_rank
        from math import comb
        for n in range(8):
            for k in range(n + 1):
                self.assertEqual(weighted_binomial_sum(n, k),
                                 sum((1 << j) * comb(n, j) for j in range(k + 1)))
        for word in ([1] * 3, [-1] * 3, [1, 1, -1], [1] * 7):
            diagram = Diagram.from_braid(2, word)
            full = khovanov_rank(diagram.pd)['by_degree']
            self.assertEqual(state_circle_count(diagram, 0), state_circle_count(diagram.mirror(), 1))
            for h in range(-1, len(word) + 2):
                result = khovanov_window_auto(diagram, h, h)
                self.assertEqual(result['by_degree'], {h: full[h]} if h in full else {})

    def test_nontrivial_window_stops_before_full_homology(self):
        diagram = Diagram.from_json(json.loads((EXAMPLES / 'conway.json').read_text()))
        module = importlib.import_module('fastunknot.recognize')
        with patch.object(module, 'khovanov_rank', side_effect=AssertionError('full scan called')):
            result = recognize(diagram, use_window=True, **ONLY_KH)
        self.assertEqual(result.status, 'KNOTTED')
        self.assertEqual(result.method, 'khovanov-window-obstruction')
        self.assertEqual(result.evidence['khovanov_window']
                         ['unreduced_rank_by_normalized_degree'], {0: 10})

    def test_rank_two_window_is_not_unknot_certificate(self):
        diagram = Diagram.from_braid(2, [-1] * 3)
        result = recognize(diagram, use_window=True, **ONLY_KH)
        self.assertEqual(result.status, 'KNOTTED')
        self.assertEqual(result.evidence['khovanov_window']['status'], 'inconclusive')
        self.assertEqual(result.method, 'reduced-khovanov-F2-scan')
        self.assertEqual(result.evidence['khovanov']['unreduced_rank'], 6)

    def test_unknot_falls_through_to_full_certificate(self):
        for diagram in (Diagram.from_braid(2, [1]), Diagram.from_braid(2, [-1]),
                        Diagram.from_braid(3, [1, -2])):
            result = recognize(diagram, use_window=True, **ONLY_KH)
            self.assertEqual(result.status, 'UNKNOT')
            self.assertEqual(result.evidence['khovanov_window']['status'], 'inconclusive')
            self.assertIn('khovanov', result.evidence)

    def test_window_limit_is_skipped_and_full_rank_still_decides(self):
        diagram = Diagram.from_braid(2, [-1] * 3)
        result = recognize(diagram, use_window=True, window_max_objects=0, **ONLY_KH)
        self.assertEqual(result.status, 'KNOTTED')
        self.assertEqual(result.evidence['khovanov_window']['status'], 'skipped')
        self.assertEqual(result.method, 'reduced-khovanov-F2-scan')

    def test_both_limits_give_unknown(self):
        diagram = Diagram.from_braid(2, [-1] * 3)
        result = recognize(diagram, use_window=True, max_objects=0, **ONLY_KH)
        self.assertEqual(result.status, 'UNKNOWN')

    def test_disabled_by_default_and_invalid_parameters(self):
        diagram = Diagram.from_braid(2, [-1] * 3)
        self.assertNotIn('khovanov_window', recognize(diagram, **ONLY_KH).evidence)
        for options in ({'window_radius': -1}, {'window_radius': True},
                        {'window_max_objects': -1}, {'window_seconds': -1}):
            with self.assertRaises(ValueError):
                recognize(diagram, **options)

    def test_cli_partial_window_has_no_total_rank_claim(self):
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            code = main(['window', str(EXAMPLES / 'conway.json'), '--lower', '6', '--upper', '6'])
        data = json.loads(output.getvalue())
        self.assertEqual(code, 0)
        self.assertEqual(data['by_degree'], {'6': 10})
        self.assertFalse(data['complete_rank'])
        self.assertNotIn('rank', data)


if __name__ == '__main__':
    unittest.main()
