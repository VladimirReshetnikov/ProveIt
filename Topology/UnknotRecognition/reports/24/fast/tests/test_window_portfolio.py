import json
from pathlib import Path
import random
import subprocess
import sys
import unittest
from unittest.mock import patch

from fastunknot import Diagram, recognize, khovanov_rank
from fastunknot.diagram import DiagramError
from fastunknot.geometry import ScanLimit
from fastunknot.window_bounds import choose_mirror, khovanov_window_auto, weighted_binomial_sum
from fastunknot.window_filter import probe_windows, window_radii
from fastunknot.window_scan import khovanov_window

ROOT = Path(__file__).resolve().parents[1]
NO_FILTERS = dict(use_braid=False, use_seifert=False, use_reduction=False, use_descending=False,
                  use_alexander=False, use_jones=False, use_factorization=False)


class WindowPortfolioTests(unittest.TestCase):
    def test_geometric_radii_and_successful_widening(self):
        self.assertEqual(list(window_radii(0)), [0])
        self.assertEqual(list(window_radii(5)), [0, 1, 2, 4, 5])
        d = Diagram.from_braid(2, [1]*3)
        single = probe_windows(d, maximum_radius=0, seconds=10)
        self.assertEqual(single['status'], 'INCONCLUSIVE')
        self.assertEqual(single['evidence']['attempts'][0]['unreduced_rank_by_normalized_degree'], {0: 2})
        wide = probe_windows(d, maximum_radius=3, seconds=10)
        self.assertEqual(wide['status'], 'KNOTTED')
        self.assertGreater(len(wide['evidence']['attempts']), 1)
        answer = recognize(d, window_radius=3, window_seconds=10, **NO_FILTERS)
        self.assertEqual(answer.status, 'KNOTTED')
        self.assertEqual(answer.method, 'khovanov-window-obstruction')

    def test_partial_agreement_falls_back_and_complete_window_decides(self):
        d = Diagram.from_braid(2, [1]*3)
        result = recognize(d, window_radius=0, window_seconds=10, **NO_FILTERS)
        self.assertEqual(result.status, 'KNOTTED')
        self.assertEqual(result.method, 'reduced-khovanov-F2-scan')
        self.assertEqual(result.evidence['khovanov_windows']['status'], 'INCONCLUSIVE')
        unknot = Diagram.from_json(json.loads((ROOT/'examples/hard_unknot_8.json').read_text()))
        probe = probe_windows(unknot, maximum_radius=8, seconds=10)
        self.assertEqual(probe['status'], 'UNKNOT')
        self.assertTrue(probe['evidence']['attempts'][-1]['complete_rank'])

    def test_local_budget_and_memory_failure_do_not_become_verdicts(self):
        d = Diagram.from_braid(2, [1]*3)
        for options in (dict(window_seconds=0), dict(window_max_objects=0)):
            result = recognize(d, window_radius=3, **options, **NO_FILTERS)
            self.assertEqual(result.status, 'KNOTTED')
            self.assertEqual(result.method, 'reduced-khovanov-F2-scan')
            self.assertEqual(result.evidence['khovanov_windows']['status'], 'INCONCLUSIVE')
        with patch('fastunknot.window_filter.khovanov_window_auto', side_effect=MemoryError):
            result = recognize(d, window_radius=3, **NO_FILTERS)
            self.assertEqual(result.status, 'KNOTTED')
            self.assertEqual(result.method, 'reduced-khovanov-F2-scan')
        self.assertEqual(recognize(d, window_radius=3, seconds=0, **NO_FILTERS).status, 'UNKNOWN')
        self.assertEqual(recognize(d, window_radius=3, max_objects=1,
                                   window_max_objects=99999, **NO_FILTERS).status, 'UNKNOWN')

    def test_shared_deadline_and_progress_heuristic(self):
        d = Diagram.from_braid(2, [1]*3)
        answer = khovanov_window_auto(d, 3, 3)
        # First query consumes 0.04 of a 0.10 allowance, leaving less than
        # twice the previous query time. The next radius must not be run.
        with patch('fastunknot.window_filter.monotonic', side_effect=[0, 0, .04, .04]):
            with patch('fastunknot.window_filter.khovanov_window_auto', return_value=answer) as run:
                result = probe_windows(d, maximum_radius=3, seconds=.1)
        self.assertEqual(run.call_count, 1)
        self.assertEqual(run.call_args.kwargs['seconds'], .1)
        self.assertIn('twice', result['evidence']['stop_reason'])
        with patch('fastunknot.window_filter.monotonic', side_effect=[0, 0, .2]):
            with patch('fastunknot.window_filter.khovanov_window_auto', side_effect=ScanLimit('local')):
                with self.assertRaisesRegex(ScanLimit, 'time budget'):
                    probe_windows(d, maximum_radius=3, seconds=1, deadline=.1)

    def test_mirror_choice_and_budget_cover_preprocessing(self):
        d = Diagram.from_braid(2, [1]*31)
        choice, data = choose_mirror(d, 31, 31)
        self.assertTrue(choice)
        self.assertLess(data['mirror_bound_bits'], data['original_bound_bits'])
        window = khovanov_window_auto(d, 31, 31)
        self.assertEqual(window['by_degree'], {31: 2})
        self.assertEqual(window['raw_lower'], 31)
        self.assertEqual(window['profile_degree_convention'], 'mirror raw')
        with patch('fastunknot.window_bounds.state_circle_count', side_effect=AssertionError('allocated')):
            with self.assertRaises(ScanLimit):
                khovanov_window_auto(d, 31, 31, seconds=0)
        self.assertEqual(weighted_binomial_sum(4, 2), 33)

    def test_current_reducers_composition_and_random_intervals(self):
        rng = random.Random(2026100805)
        accepted = 0
        while accepted < 100:
            b = rng.randrange(2, 6)
            word = [rng.choice((-1, 1))*rng.randrange(1, b) for _ in range(rng.randrange(1, 13))]
            try:
                d = Diagram.from_braid(b, word)
            except DiagramError:
                continue
            order = list(range(len(word)))
            rng.shuffle(order)
            full = khovanov_rank(d.pd, order=order)['by_degree']
            lo = rng.randrange(-1, len(word)+2)
            hi = lo + rng.randrange(4)
            expected = {h: count for h, count in full.items() if lo <= h <= hi}
            for reduction in ('standard', 'residue', 'adaptive'):
                result = khovanov_window_auto(d, lo, hi, order=order,
                    reduction=reduction, composition='component-dense' if accepted < 20 else 'standard',
                    check_d_squared=True)
                self.assertEqual(result['by_degree'], expected, (word, order, lo, hi, reduction))
            accepted += 1

    def test_pipeline_evidence_tied_to_factor(self):
        d = Diagram.from_json(json.loads((ROOT/'examples/conway_sum_2.json').read_text()))
        options = dict(NO_FILTERS, use_factorization=True)
        result = recognize(d, window_radius=0, window_seconds=10, **options)
        self.assertEqual(result.status, 'KNOTTED')
        # The first nontrivial factor decides the connected sum.
        found = []
        def walk(value):
            if isinstance(value, dict):
                if 'khovanov_windows' in value:
                    found.append(value['khovanov_windows'])
                for child in value.values():
                    walk(child)
            elif isinstance(value, list):
                for child in value:
                    walk(child)
        walk(result.evidence)
        self.assertTrue(found)
        evidence = found[0]
        factor = Diagram.from_pd(evidence['diagram_pd'])
        self.assertLess(factor.crossings, d.crossings)
        self.assertEqual(probe_windows(factor, maximum_radius=0, seconds=10)['status'], 'KNOTTED')

    def test_validation_and_cli(self):
        d = Diagram.from_braid(2, [1]*3)
        for options in (dict(window_radius=-1), dict(window_radius=True), dict(window_max_objects=-1),
                        dict(window_seconds=float('nan')), dict(window_seconds=float('inf'))):
            with self.assertRaises(ValueError):
                recognize(d, **options)
        for options in (dict(reduction='invalid'), dict(composition='invalid'), dict(seconds=-1)):
            with self.assertRaises(ValueError):
                khovanov_window(d.pd, 0, 0, **options)
        data = json.dumps({'braid': {'strands': 2, 'word': [1]*3}})
        command = [sys.executable, '-m', 'fastunknot', 'window', '-', '--normalized', '--auto-mirror']
        result = subprocess.run(command, input=data, text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout)['normalized_by_degree'], {'0': 2})
        self.assertFalse(json.loads(result.stdout)['complete_rank'])
        for args, code in ((['--seconds', '0'], 3), (['--lower', '2', '--upper', '1'], 2)):
            result = subprocess.run(command + args, input=data, text=True, capture_output=True)
            self.assertEqual(result.returncode, code, result.stderr)


if __name__ == '__main__':
    unittest.main()

