"""Exhaustive small commutants validate the generated-local-algebra stop."""
import unittest
from fastunknot.barcode_scan import _apply
from fastunknot.component_scan import components
from fastunknot.scalar_split import (FittingScan, _columns, find_scalar_split,
                                    scalar_endomorphism_space)
from fastunknot.primary_split import primary_projector


def quiver(matrix):
    n = len(matrix)
    scan = FittingScan()
    m = scan.algebra.intern(((0, 1), (2, 3)))
    scan.points = frozenset(range(4))
    scan.mid = [m] * (2*n)
    scan.deg = [0]*n + [1]*n
    scan.out = [{} for _ in scan.mid]
    scan.inc = [set() for _ in scan.mid]
    for j in range(n):
        for i in range(n):
            value = (2 if i == j else 0) ^ (4 if matrix[j] >> i & 1 else 0)
            if value:
                scan.out[j][n+i] = value
                scan.inc[n+i].add(j)
    scan.live = 2*n
    scan.owner = [0] * scan.live
    scan.weights = [{0: 1}]
    return scan


class PrimaryLocalStopTests(unittest.TestCase):
    def test_complete_local_certificates_against_every_small_endomorphism(self):
        certified = checked = 0
        for packed in range(16):
            scan = quiver([packed & 3, packed >> 2])
            for group in components(scan):
                blocks, variables, basis, _ = scalar_endomorphism_space(scan, group)
                out, witness, metrics = find_scalar_split(scan, group, primary=True)
                if not metrics['primary_local_certificates']:
                    continue
                self.assertIsNone(out)
                self.assertIsNone(witness)
                proof = metrics['primary_local_certificate']
                self.assertEqual(proof['commutant_dimension'], len(basis))
                self.assertEqual(proof['minimal_degree'], len(basis))
                self.assertEqual(proof['berlekamp_dimension'], 1)
                projector, independent = primary_projector(proof['candidate_columns'])
                self.assertIsNone(projector)
                self.assertEqual(independent['minimal_polynomial'], proof['minimal_polynomial'])
                identity = [[1 << i for i in range(len(b))] for b in blocks]
                zero = [[0]*len(b) for b in blocks]
                for coefficients in range(1 << len(basis)):
                    vector = 0
                    for i, item in enumerate(basis):
                        if coefficients >> i & 1:
                            vector ^= item
                    matrices = _columns(blocks, variables, vector)
                    squared = [[_apply(m, c) for c in m] for m in matrices]
                    if squared == matrices:
                        self.assertIn(matrices, (zero, identity))
                    checked += 1
                certified += 1
        self.assertGreaterEqual(certified, 2)
        self.assertGreaterEqual(checked, 8)

    def test_primary_nongenerator_cannot_certify_the_whole_commutant(self):
        # Two copies of F4: Q has irreducible minimal polynomial of degree 2,
        # but its commutant contains all 2x2 matrices over F4 (dimension 8).
        scan = quiver([2, 3, 8, 12])
        group = list(range(scan.live))
        space = scalar_endomorphism_space(scan, group)
        self.assertEqual(len(space[2]), 8)
        self.assertIsNone(primary_projector([[2, 3, 8, 12]])[0])
        rows, witness, metrics = find_scalar_split(scan, group, primary=True)
        self.assertIsNotNone(rows)
        self.assertIsNotNone(witness)
        self.assertEqual(metrics['primary_local_certificates'], 0)


if __name__ == '__main__':
    unittest.main()
