"""Check the residue prediction against actual topological cancellations."""
import random
import unittest

from fastunknot.diagram import Diagram, DiagramError
from fastunknot.ordering import best_scan_order
from fastunknot.residue import object_profile, residue_profile
from fastunknot.scan import ScanComplex
from fastunknot.scan_fast import FastScan


class ResidueTests(unittest.TestCase):
    def test_canonical_multiplicities_across_pivots_and_encodings(self):
        rng = random.Random(3270)
        diagrams = [Diagram.from_braid(3, [1, -2] * 4),
                    Diagram.from_braid(3, [1, 2] * 5)]
        while len(diagrams) < 18:
            strands = rng.choice((3, 4))
            word = [rng.choice((-1, 1)) * rng.randrange(1, strands)
                    for _ in range(rng.randrange(4, 11))]
            try:
                diagrams.append(Diagram.from_braid(strands, word))
            except DiagramError:
                continue
        self.checked_prefixes = 0
        for diagram in diagrams:
            scanners = [FastScan(), ScanComplex(pivot="minfill"),
                        ScanComplex(pivot="lifo"),
                        ScanComplex(pivot="lifo", algebra="sets")]
            for crossing in best_scan_order(diagram.pd):
                profiles = []
                for scan in scanners:
                    scan.add_crossing(diagram.pd[crossing], reduce_now=False)
                    predicted = residue_profile(scan, check_squared=True)
                    scan.eliminate()
                    actual = object_profile(scan)
                    self.assertEqual(predicted, actual)
                    self.assertEqual(residue_profile(scan), actual)
                    profiles.append(predicted)
                for profile in profiles[1:]:
                    self.assertEqual(profiles[0], profile)
                self.checked_prefixes += 1
        self.assertGreater(self.checked_prefixes, 90)

    def test_uncancelled_closed_complex_agrees_with_full_linear_homology(self):
        diagram = Diagram.from_braid(3, [1, -2] * 2)
        scan = FastScan()
        for slots in diagram.pd:
            scan.add_crossing(slots, reduce_now=False)
        profile = residue_profile(scan, check_squared=True)
        self.assertTrue(all(matching == () for matching, _ in profile))
        self.assertEqual({degree: value for (_, degree), value in profile.items()},
                         scan.linear_ranks())

    def test_empty_complex_and_nonmutation(self):
        scan = FastScan()
        before = (list(scan.mid), list(scan.deg), [dict(row) for row in scan.out])
        self.assertEqual(residue_profile(scan), {((), 0): 1})
        after = (list(scan.mid), list(scan.deg), [dict(row) for row in scan.out])
        self.assertEqual(before, after)


if __name__ == "__main__":
    unittest.main()
