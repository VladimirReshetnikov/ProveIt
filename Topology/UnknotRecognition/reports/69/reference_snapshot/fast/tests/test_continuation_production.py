import json
from pathlib import Path
import subprocess
import sys
import unittest
from unittest.mock import patch

from fastunknot import Diagram, recognize, khovanov_rank
from fastunknot.barcode_scan import barcode_khovanov_rank, barcode_khovanov_decide
from fastunknot.scalar_split import FittingScan, scalar_endomorphism_space, _scalar_key
from fastunknot.scalar_split import fitting_khovanov_rank, fitting_khovanov_decide
from fastunknot.recovered_grading import recover_shifts
from fastunknot.geometry import ScanLimit
from test_barcode_scan import make_connected_ladder
from test_scalar_split import mixed_copies, verify_witness

ROOT = Path(__file__).resolve().parents[1]
NO_FILTERS = dict(use_braid=False, use_seifert=False, use_reduction=False,
                  use_descending=False, use_alexander=False, use_jones=False,
                  use_factorization=False)


class ContinuationProductionTests(unittest.TestCase):
    def test_grading_restricts_blocks_and_rejects_mixed_entries_and_cycles(self):
        scan = make_connected_ladder(FittingScan, 2, 2)
        scan.out = [{2: 2}, {2: 8}, {}, {}]
        scan.inc = [set(), set(), {0, 1}, set()]
        group = [0, 1, 2]
        q = recover_shifts(scan, group)
        self.assertNotEqual(q[0], q[1])
        graded = scalar_endomorphism_space(scan, group)
        plain = scalar_endomorphism_space(scan, group, preserve_grading=False)
        self.assertEqual(len(graded[1]), 3)
        self.assertEqual(len(plain[1]), 5)
        self.assertNotEqual(_scalar_key(scan, group), _scalar_key(scan, group, False))
        scan.out[1][2] = 2 | 8
        with self.assertRaisesRegex(ValueError, 'homogeneous'):
            recover_shifts(scan, group)
        scan.out = [{2: 2, 3: 2}, {2: 2, 3: 8}, {}, {}]
        with self.assertRaisesRegex(ValueError, 'cycle'):
            recover_shifts(scan, [0, 1, 2, 3])

    def test_recovery_matches_independent_shadow_labels(self):
        from audit_grading import GradingAuditScan
        from fastunknot.component_scan import components
        for name in ('conway', 'kinoshita_terasaka', 'hard_unknot_8'):
            d = Diagram.from_json(json.loads((ROOT/'examples'/(name+'.json')).read_text()))
            scan = GradingAuditScan()
            for row in d.pd:
                scan.add_crossing(row)
                for group in components(scan):
                    q = recover_shifts(scan, group)
                    offsets = {q[v] - scan.qshift[v] for v in group}
                    self.assertEqual(len(offsets), 1)

    def test_witness_quantum_corruption_and_cache_modes(self):
        scan = mixed_copies(FittingScan, 3, record_witnesses=True)
        scan._compress([0]*scan.live)
        for witness in scan.fitting_witnesses:
            self.assertTrue(verify_witness(witness))
            # All original source labels in this fixture have the same shift.
            witness['quantum_shifts'] = list(range(len(witness['rows'])))
            with self.assertRaises(AssertionError):
                verify_witness(witness)
        ungraded = mixed_copies(FittingScan, 3, preserve_grading=False)
        ungraded._compress([0]*ungraded.live)
        self.assertFalse(set(scan.scalar_cache) & set(ungraded.scalar_cache))

    def test_api_budgets_validation_and_order_charge(self):
        d = Diagram.from_braid(2, [1]*3)
        for run in (barcode_khovanov_rank, fitting_khovanov_rank,
                    barcode_khovanov_decide, fitting_khovanov_decide):
            for pd in ([], d.pd):
                for options in (dict(seconds=float('nan')), dict(seconds=-1), dict(max_objects=-1)):
                    with self.assertRaises(ValueError):
                        run(pd, **options)
            with self.assertRaises(ScanLimit):
                run(d.pd, seconds=0)
            with self.assertRaises(ScanLimit):
                run(d.pd, max_objects=0)
        for run in (fitting_khovanov_rank, fitting_khovanov_decide):
            with self.assertRaises(ValueError):
                run([], fitting_max_objects=-1)
        with self.assertRaises(ValueError):
            barcode_khovanov_decide([], length_cap=1)
        def planner(pd, *, tries, check):
            check()
            return list(range(len(pd)))
        with patch('fastunknot.scalar_split.monotonic', side_effect=[0, 0, 2]):
            with patch('fastunknot.scalar_split.best_scan_order', side_effect=planner):
                with self.assertRaises(ScanLimit):
                    fitting_khovanov_rank(d.pd, seconds=1)

    def test_pipeline_and_cli_keep_exact_and_capped_contracts_separate(self):
        d = Diagram.from_braid(2, [1]*3)
        for backend in ('barcode', 'fitting'):
            r = recognize(d, backend=backend, **NO_FILTERS)
            self.assertEqual(r.status, 'KNOTTED')
            self.assertEqual(r.evidence['khovanov']['rank_capped'], 3)
            self.assertNotIn('by_degree', r.evidence['khovanov'])
            self.assertNotIn('rank', r.evidence['khovanov'])
            r = recognize(d, backend=backend, window_radius=0, window_seconds=1, **NO_FILTERS)
            self.assertEqual(r.status, 'KNOTTED')
            self.assertIn('khovanov_windows', r.evidence)
            self.assertEqual(recognize(d, backend=backend, max_objects=0, **NO_FILTERS).status, 'UNKNOWN')
            with self.assertRaises(ValueError):
                recognize(d, backend=backend, reduction='adaptive')
            command = [sys.executable, '-B', '-m', 'fastunknot', 'khovanov', '-', '--'+backend]
            data = json.dumps(dict(braid=dict(strands=2, word=[1]*3)))
            p = subprocess.run(command, input=data, text=True, capture_output=True)
            self.assertEqual(p.returncode, 0, p.stderr)
            result = json.loads(p.stdout)
            self.assertEqual(result['rank'], khovanov_rank(d.pd)['rank'])
            self.assertIn('by_degree', result)
            self.assertNotIn('rank_capped', result)
            for option in ('--shared', '--twist', '--factor', '--barcode' if backend=='fitting' else '--fitting'):
                p = subprocess.run(command+[option], input=data, text=True, capture_output=True)
                self.assertEqual(p.returncode, 2)
