from pathlib import Path
import sys,unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'experiments'))
from common import *
from descending_grid import *
from disk_frontier import *
from certified_driver import component_count

class GridTests(unittest.TestCase):
    def test_grid_certificates_and_planarity(self):
        for m in range(1,9):
            pd=descending_grid(m)
            self.assertEqual(len(pd),m*m)
            self.assertEqual(component_count(pd),1)
            self.assertEqual(len(verify_descending(pd)),2*m*m)
            validate_connected_cut_order(pd,bipolar_order(pd))

    def test_small_grids_independent_homology(self):
        for m in (1,2,3):self.assertEqual(sum(cube_ranks(descending_grid(m)).values()),2)

    def test_corrupted_descending_assignment(self):
        pd=descending_grid(2);pd[1]=pd[1][1:]+pd[1][:1]
        with self.assertRaises(ValueError):verify_descending(pd)

    def test_bad_size(self):
        for m in (0,-1,True,1.5):
            with self.assertRaises(ValueError):descending_grid(m)

if __name__=='__main__':unittest.main()
