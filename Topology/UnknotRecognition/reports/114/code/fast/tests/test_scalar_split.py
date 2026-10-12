"""Independent dense witness verification for scalar Fitting splits."""
import copy
import json
import pathlib
import random
import sys
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from fastunknot import Diagram, khovanov_rank
from fastunknot.component_scan import ComponentScan
from fastunknot.scalar_split import (FittingScan, binary_nullspace,
    fitting_khovanov_rank, fitting_khovanov_decide, scalar_endomorphism_space)
from test_barcode_scan import dense_rank


def xor_rows(left, right):
    return [a ^ b for a, b in zip(left, right)]


def left_scalar(scalar, coefficients):
    out = [[0] * len(coefficients[0]) for _ in scalar]
    for i, row in enumerate(scalar):
        for k, bit in enumerate(row):
            if bit:
                out[i] = xor_rows(out[i], coefficients[k])
    return out


def transpose(matrix):
    return list(map(list, zip(*matrix)))


def right_scalar(coefficients, scalar):
    return transpose(left_scalar(transpose(scalar), transpose(coefficients)))


def dense_inverse(matrix):
    n = len(matrix)
    rows = [list(row) + [int(i == j) for j in range(n)] for i, row in enumerate(matrix)]
    for col in range(n):
        pivot = next(i for i in range(col, n) if rows[i][col])
        rows[col], rows[pivot] = rows[pivot], rows[col]
        for i in range(n):
            if i != col and rows[i][col]:
                rows[i] = xor_rows(rows[i], rows[col])
    return [row[n:] for row in rows]


def unpack(blocks, columns, n):
    matrix = [[0] * n for _ in range(n)]
    for block, cols in zip(blocks, columns):
        for col, source in enumerate(block):
            for row, target in enumerate(block):
                matrix[target][source] = (cols[col] >> row) & 1
    return matrix


def differential(rows):
    n = len(rows)
    return [[rows[source].get(target, rows[source].get(str(target), 0))
             for source in range(n)] for target in range(n)]


def verify_witness(witness):
    """Dense independent verifier; accepts an in-memory or JSON-roundtripped witness."""
    n = len(witness['rows'])
    q = unpack(witness['blocks'], witness['endomorphism_columns'], n)
    s = unpack(witness['blocks'], witness['basis_columns'], n)
    inverse = dense_inverse(s)
    d = differential(witness['rows'])
    transformed = differential(witness['transformed_rows'])
    for i in range(n):
        for j in range(n):
            if s[i][j] or q[i][j]:
                assert witness['degrees'][i] == witness['degrees'][j]
                assert witness['matchings'][i] == witness['matchings'][j]
                if witness.get('preserves_quantum_grading'):
                    assert witness['quantum_shifts'][i] == witness['quantum_shifts'][j]
    assert left_scalar(q, d) == right_scalar(d, q)
    assert left_scalar(inverse, right_scalar(d, s)) == transformed
    assert left_scalar(s, right_scalar(transformed, inverse)) == d
    for i in range(n):
        for j in range(n):
            if witness['sides'][i] != witness['sides'][j]:
                assert transformed[i][j] == 0
    assert 0 < sum(witness['sides']) < n
    return True


def mixed_copies(scan_class, copies, **options):
    scan = scan_class(shape_cache=False, **options)
    a = scan.algebra.intern(((0, 1), (2, 3)))
    b = scan.algebra.intern(((0, 3), (1, 2)))
    scan.points = frozenset(range(4))
    scan.mid = [m for _ in range(copies) for m in (a, a, b)]
    scan.deg = [h for _ in range(copies) for h in (0, 1, 1)]
    scan.out = [{} for _ in scan.mid]
    # An upper-triangular scalar change of basis hides the copies in one
    # connected graph with multiple matching types and morphism coefficients.
    for j in range(copies):
        for i in range(j + 1):
            scan.out[3 * j][3 * i + 1] = 2
            scan.out[3 * j][3 * i + 2] = 1
    scan.inc = [set() for _ in scan.mid]
    for source, row in enumerate(scan.out):
        for target in row:
            scan.inc[target].add(source)
    scan.live = len(scan.mid)
    scan.owner = [0] * scan.live
    scan.weights = [{0: 1}]
    return scan


class BinaryTests(unittest.TestCase):
    def test_nullspaces_against_dense_rank(self):
        rng = random.Random(49205)
        for _ in range(100):
            variables = rng.randrange(1, 15)
            rows = [rng.randrange(1 << variables) for _ in range(rng.randrange(20))]
            basis = binary_nullspace(rows, variables)
            rank = dense_rank([[(row >> i) & 1 for i in range(variables)] for row in rows])
            self.assertEqual(len(basis), variables - rank)
            self.assertTrue(all((row & v).bit_count() % 2 == 0 for row in rows for v in basis))
            self.assertEqual(dense_rank([[(v >> i) & 1 for i in range(variables)] for v in basis]), len(basis))


class FittingTests(unittest.TestCase):
    def test_mixed_matching_attached_copies_split_exactly(self):
        for copies in [2, 3, 6]:
            old = mixed_copies(ComponentScan, copies)
            scan = mixed_copies(FittingScan, copies, record_witnesses=True)
            old._compress([0] * old.live)
            scan._compress([0] * scan.live)
            self.assertEqual(old.live, 3 * copies)
            self.assertGreater(scan.stats['fitting_splits'], 0)
            self.assertLessEqual(scan.live, old.live)
            self.assertEqual(sum(len(row) for row in scan.out), 2 * len(scan.weights))
            self.assertEqual(sum(sum(w.values()) for w in scan.weights), copies)
            for witness in scan.fitting_witnesses:
                self.assertTrue(verify_witness(witness))
                self.assertTrue(verify_witness(json.loads(json.dumps(witness))))
            scan.check_d_squared()

    def test_cache_reuse_and_limits(self):
        scan = mixed_copies(FittingScan, 3, record_witnesses=True)
        scan._compress([0] * scan.live)
        cached = dict(scan.scalar_cache)
        again = mixed_copies(FittingScan, 3, record_witnesses=True)
        again.scalar_cache = cached
        again._compress([0] * again.live)
        self.assertGreater(again.stats['fitting_cache_hits'], 0)
        self.assertEqual(again.live, scan.live)
        self.assertEqual(again.weights, scan.weights)
        for witness in again.fitting_witnesses:
            self.assertTrue(verify_witness(witness))
        skipped = mixed_copies(FittingScan, 3, fitting_max_objects=8)
        skipped._compress([0] * skipped.live)
        self.assertEqual(skipped.live, 9)
        self.assertEqual(skipped.stats['fitting_splits'], 0)
        self.assertIsNone(scalar_endomorphism_space(mixed_copies(FittingScan, 3), list(range(9)), max_variables=1))

    def test_named_actual_witnesses_and_corruption(self):
        for name in ['conway', 'kinoshita_terasaka']:
            diagram = Diagram.from_json(json.loads((ROOT / 'examples' / (name + '.json')).read_text()))
            normal = fitting_khovanov_rank(diagram.pd, record_witnesses=True, check_d_squared=True)
            old = khovanov_rank(diagram.pd)
            self.assertEqual(normal['rank'], old['rank'])
            self.assertEqual(normal['by_degree'], old['by_degree'])
            self.assertTrue(normal['witnesses'])
            for witness in normal['witnesses']:
                self.assertTrue(verify_witness(witness))
            broken = copy.deepcopy(normal['witnesses'][0])
            broken['transformed_rows'][0][0] = broken['transformed_rows'][0].get(0, 0) ^ 1
            with self.assertRaises(AssertionError):
                verify_witness(broken)

    def test_random_braids_and_capped_model(self):
        rng = random.Random(38266)
        tested = 0
        while tested < 80:
            strands = rng.randrange(2, 7)
            word = [rng.choice([-1, 1]) * rng.randrange(1, strands)
                    for _ in range(rng.randrange(3, 18))]
            try:
                diagram = Diagram.from_braid(strands, word)
            except ValueError:
                continue
            order = list(range(len(word)))
            if tested % 3 == 0:
                rng.shuffle(order)
            old = khovanov_rank(diagram.pd, order=order)
            normal = fitting_khovanov_rank(diagram.pd, order=order, check_d_squared=True)
            capped = fitting_khovanov_decide(diagram.pd, order=order, check_d_squared=True)
            self.assertEqual(normal['rank'], old['rank'])
            self.assertEqual(normal['by_degree'], old['by_degree'])
            self.assertEqual(capped['rank_capped'], min(3, old['rank']))
            tested += 1


if __name__ == '__main__':
    unittest.main(verbosity=2)
