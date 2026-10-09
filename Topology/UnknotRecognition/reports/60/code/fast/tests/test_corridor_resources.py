"""A failed full transfer never installs only part of its replacement graph."""
import copy
import importlib
import unittest
from unittest.mock import patch

from fastunknot.geometry import ScanLimit
from fastunknot.corridor import CorridorScan
from test_graded_transfer_integration import small_complex


class CorridorResourceTests(unittest.TestCase):
    def test_expiry_after_transfer_preserves_current_differential(self):
        module = importlib.import_module('fastunknot.corridor')
        scan = small_complex(CorridorScan, [0,0,1,1], [0,0,0,2],
                             [{2:1,3:2},{2:1},{},{}])
        before = copy.deepcopy((scan.mid, scan.deg, scan.qshift, scan.out, scan.inc, scan.live))
        real_transfer = module.corridor_transfer

        def expired(*args, **kwargs):
            result = real_transfer(*args, **kwargs)
            scan.deadline = 0
            return result

        with patch.object(module, 'corridor_transfer', side_effect=expired):
            with self.assertRaises(ScanLimit):
                scan.eliminate()
        self.assertEqual((scan.mid, scan.deg, scan.qshift, scan.out, scan.inc, scan.live), before)
        scan.deadline = None
        scan.eliminate()
        self.assertEqual(scan.out, [{1:2},{}])

    def test_reverse_index_allocation_failure_preserves_current_differential(self):
        scan = small_complex(CorridorScan, [0,0,1,1], [0,0,0,2],
                             [{2:1,3:2},{2:1},{},{}])
        before = copy.deepcopy((scan.mid, scan.deg, scan.qshift, scan.out, scan.inc, scan.live))
        module = importlib.import_module('fastunknot.corridor')
        completed = module.corridor_transfer(scan)
        with patch.object(module, 'corridor_transfer', return_value=completed):
            with patch('fastunknot.corridor.set', side_effect=MemoryError, create=True):
                with self.assertRaises(MemoryError):
                    scan.eliminate()
        self.assertEqual((scan.mid, scan.deg, scan.qshift, scan.out, scan.inc, scan.live), before)
        scan.eliminate()
        self.assertEqual(scan.out, [{1:2},{}])

    def test_zero_profile_allocation_failure_preserves_differential(self):
        from fastunknot.graded import GradedResidueScan
        scan = small_complex(GradedResidueScan, [0,0,1,1], [2,0,0,0],
                             [{},{2:1},{},{}])
        before = copy.deepcopy((scan.mid, scan.deg, scan.qshift, scan.out, scan.inc, scan.live))
        with patch('fastunknot.graded.set', side_effect=MemoryError, create=True):
            with self.assertRaises(MemoryError):
                scan.eliminate()
        self.assertEqual((scan.mid, scan.deg, scan.qshift, scan.out, scan.inc, scan.live), before)
        scan.eliminate()
        self.assertEqual(scan.live, 2)
        self.assertFalse(any(scan.out))

    def test_adaptive_switch_keeps_completed_pivots_and_nonzero_map(self):
        from benchmark_residue import dense_two_term
        from fastunknot.corridor import AdaptiveCorridorScan
        scan = dense_two_term(AdaptiveCorridorScan, 32, graded=True)
        scan.qshift = [0] * len(scan.mid)
        a = len(scan.mid)
        scan.mid.extend([scan.mid[0], scan.mid[0]])
        scan.deg.extend([0,1])
        scan.qshift.extend([0,2])
        scan.out.extend([{a+1:2}, {}])
        scan.inc.extend([set(), {a}])
        scan.live += 2
        scan.eliminate()
        self.assertEqual(scan.live, 3)
        self.assertGreater(scan.stats['schur_update_pairs'], 0)
        self.assertEqual(scan.stats['corridor_switches'], 1)
        self.assertEqual(scan.stats['corridor_stages'], 1)
        self.assertLess(scan.history[0]['before'], a + 2)
        self.assertEqual([value for row in scan.out for value in row.values()], [2])
        scan.check_d_squared()
        scan.check_grading()


if __name__ == '__main__':
    unittest.main()
