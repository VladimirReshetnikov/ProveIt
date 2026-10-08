"""A failed full transfer never installs only part of its replacement graph."""
import copy
import importlib
import unittest
from unittest.mock import patch

from fastunknot.geometry import ScanLimit
from fastunknot.graded_transfer import GradedTransferScan
from test_graded_transfer_integration import small_complex


class GradedTransferResourceTests(unittest.TestCase):
    def test_expiry_after_transfer_preserves_current_differential(self):
        module = importlib.import_module('fastunknot.graded_transfer')
        scan = small_complex(GradedTransferScan, [0,0,1,1], [0,0,0,2],
                             [{2:1,3:2},{2:1},{},{}])
        before = copy.deepcopy((scan.mid, scan.deg, scan.qshift, scan.out, scan.inc, scan.live))
        real_transfer = module.transfer

        def expired(*args, **kwargs):
            result = real_transfer(*args, **kwargs)
            scan.deadline = 0
            return result

        with patch.object(module, 'transfer', side_effect=expired):
            with self.assertRaises(ScanLimit):
                scan.eliminate()
        self.assertEqual((scan.mid, scan.deg, scan.qshift, scan.out, scan.inc, scan.live), before)
        scan.deadline = None
        scan.eliminate()
        self.assertEqual(scan.out, [{1:2},{}])

    def test_reverse_index_allocation_failure_preserves_current_differential(self):
        scan = small_complex(GradedTransferScan, [0,0,1,1], [0,0,0,2],
                             [{2:1,3:2},{2:1},{},{}])
        before = copy.deepcopy((scan.mid, scan.deg, scan.qshift, scan.out, scan.inc, scan.live))
        with patch('fastunknot.graded_transfer.set', side_effect=MemoryError, create=True):
            with self.assertRaises(MemoryError):
                scan.eliminate()
        self.assertEqual((scan.mid, scan.deg, scan.qshift, scan.out, scan.inc, scan.live), before)
        scan.eliminate()
        self.assertEqual(scan.out, [{1:2},{}])


if __name__ == '__main__':
    unittest.main()
