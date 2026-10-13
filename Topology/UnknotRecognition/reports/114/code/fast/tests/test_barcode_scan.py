"""Independent finite linear algebra and scanner checks for interval sharing."""
import json
import pathlib
import random
import sys
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from fastunknot import Diagram, khovanov_rank
from fastunknot.barcode_scan import BarcodeScan, interval_multiplicities, barcode_khovanov_rank, barcode_khovanov_decide
from fastunknot.component_scan import ComponentScan


def dense_rank(matrix):
    """Elementary row elimination; intentionally independent of packed basis code."""
    matrix = [list(row) for row in matrix]
    if not matrix:
        return 0
    rank = 0
    for column in range(len(matrix[0])):
        pivot = next((i for i in range(rank, len(matrix)) if matrix[i][column]), None)
        if pivot is None:
            continue
        matrix[rank], matrix[pivot] = matrix[pivot], matrix[rank]
        for i in range(rank + 1, len(matrix)):
            if matrix[i][column]:
                matrix[i] = [a ^ b for a, b in zip(matrix[i], matrix[rank])]
        rank += 1
    return rank


def interval_matrices(intervals, length):
    active = [[(a, b, c) for a, b, copies in intervals for c in range(copies) if a <= h <= b]
              for h in range(length)]
    arrows = []
    for h in range(length - 1):
        target = {name: i for i, name in enumerate(active[h + 1])}
        arrows.append([1 << target[name] if name in target else 0 for name in active[h]])
    return list(map(len, active)), arrows


def dense(columns, targets):
    return [[(column >> r) & 1 for column in columns] for r in range(targets)]


def packed(matrix, sources):
    return [sum(row[c] << r for r, row in enumerate(matrix)) for c in range(sources)]


def random_basis_change(dimensions, arrows, rng):
    matrices = [dense(columns, dimensions[h + 1]) for h, columns in enumerate(arrows)]
    for h, dimension in enumerate(dimensions):
        if dimension < 2:
            continue
        for _ in range(5 * dimension):
            i, j = rng.sample(range(dimension), 2)
            if h:
                matrices[h - 1][i] = [a ^ b for a, b in zip(matrices[h - 1][i], matrices[h - 1][j])]
            if h < len(matrices):
                for row in matrices[h]:
                    row[j] ^= row[i]
    return [packed(matrix, dimensions[h]) for h, matrix in enumerate(matrices)]


def totalized_homology(dimensions, arrows, suffix_dims, suffix_arrows):
    """Dense closure oracle over A=F2[x]/x².

    In suffix degree q use A^suffix_dims[q], with differential x N_q.
    The common nilpotent theta acts by multiplication x.  Totalize the
    arbitrary quiver with this suffix and compute homology by dense matrices.
    The scalar N_q are arbitrary and need not square to zero: x²=0 ensures it.
    """
    objects = {}
    for h, dh in enumerate(dimensions):
        for q, dq in enumerate(suffix_dims):
            objects.setdefault(h + q, []).extend((h, q, a, b, dot)
                for a in range(dh) for b in range(dq) for dot in range(2))
    ranks = {}
    for k, sources in objects.items():
        targets = objects.get(k + 1, [])
        lookup = {item: i for i, item in enumerate(targets)}
        matrix = [[0] * len(sources) for _ in targets]
        for c, (h, q, a, b, dot) in enumerate(sources):
            if dot:
                continue
            if h + 1 < len(dimensions):
                for a2 in range(dimensions[h + 1]):
                    if arrows[h][a] >> a2 & 1:
                        matrix[lookup[h + 1, q, a2, b, 1]][c] ^= 1
            if q + 1 < len(suffix_dims):
                for b2 in range(suffix_dims[q + 1]):
                    if suffix_arrows[q][b] >> b2 & 1:
                        matrix[lookup[h, q + 1, a, b2, 1]][c] ^= 1
        ranks[k] = dense_rank(matrix)
    return {k: len(group) - ranks.get(k - 1, 0) - ranks.get(k, 0)
            for k, group in objects.items()}


def make_connected_ladder(scan_class, copies, layers=2, rank_cap=None, **options):
    """Each binary arrow is invertible bidiagonal; the whole graph is connected."""
    scan = scan_class(shape_cache=False, rank_cap=rank_cap, **options)
    matching = scan.algebra.intern(((0, 1), (2, 3)))
    scan.points = frozenset(range(4))
    count = copies * layers
    scan.mid = [matching] * count
    scan.deg = [h for h in range(layers) for _ in range(copies)]
    scan.out = [{} for _ in range(count)]
    theta = 2                                  # x on the first component
    for h in range(layers - 1):
        for i in range(copies):
            row = scan.out[h * copies + i]
            row[(h + 1) * copies + i] = theta
            if i + 1 < copies:
                row[(h + 1) * copies + i + 1] = theta
    scan.inc = [set() for _ in range(count)]
    for v, row in enumerate(scan.out):
        for w in row:
            scan.inc[w].add(v)
    scan.live = count
    scan.weights = [{0: 1}]
    scan.owner = [0] * count
    return scan


class RankInvariantTests(unittest.TestCase):
    def test_known_intervals_under_independent_basis_changes(self):
        rng = random.Random(83029)
        for _ in range(80):
            length = rng.randrange(1, 6)
            expected = [(a, b, rng.randrange(1, 3)) for a in range(length)
                        for b in range(a, length) if rng.randrange(4) == 0]
            dimensions, arrows = interval_matrices(expected, length)
            arrows = random_basis_change(dimensions, arrows, rng)
            actual, ranks = interval_multiplicities(dimensions, arrows)
            self.assertEqual(actual, expected)
            for (i, j), rank in ranks.items():
                self.assertEqual(rank, sum(c for a, b, c in expected if a <= i and j <= b))

    def test_arbitrary_quivers_and_dense_suffix_closures(self):
        rng = random.Random(32917)
        for _ in range(60):
            length = rng.randrange(1, 5)
            dimensions = [rng.randrange(1, 5) for _ in range(length)]
            arrows = [[rng.randrange(1 << dimensions[h + 1]) for _ in range(dimensions[h])]
                      for h in range(length - 1)]
            intervals, ranks = interval_multiplicities(dimensions, arrows)
            rebuilt_dims, rebuilt_arrows = interval_matrices(intervals, length)
            self.assertEqual(dimensions, rebuilt_dims)
            for h, columns in enumerate(arrows):
                self.assertEqual(ranks[h, h + 1], dense_rank(dense(columns, dimensions[h + 1])))
            suffix_dims = [rng.randrange(1, 4) for _ in range(rng.randrange(1, 4))]
            suffix_arrows = [[rng.randrange(1 << suffix_dims[h + 1]) for _ in range(suffix_dims[h])]
                             for h in range(len(suffix_dims) - 1)]
            self.assertEqual(totalized_homology(dimensions, arrows, suffix_dims, suffix_arrows),
                             totalized_homology(rebuilt_dims, rebuilt_arrows, suffix_dims, suffix_arrows))

    def test_not_a_binary_chain_complex(self):
        # B1 B0 is nonzero; theta² makes the original differential square zero.
        intervals, ranks = interval_multiplicities([1, 1, 1], [[1], [1]])
        self.assertEqual(intervals, [(0, 2, 1)])
        self.assertEqual(ranks[0, 2], 1)

    def test_invalid_input(self):
        for dimensions, arrows in [([-1], []), ([1, 1], []), ([1, 1], [[2]]), ([1, 1], [[]])]:
            with self.assertRaises(ValueError):
                interval_multiplicities(dimensions, arrows)


class NormalizerTests(unittest.TestCase):
    def test_connected_ladder_splits_and_shares(self):
        for layers in [2, 3, 7]:
            for copies in [2, 7, 31]:
                reference = make_connected_ladder(ComponentScan, copies, layers)
                normal = make_connected_ladder(BarcodeScan, copies, layers)
                reference._compress([0] * reference.live)
                normal._compress([0] * normal.live)
                self.assertEqual(reference.live, copies * layers)
                self.assertEqual(normal.live, layers)
                self.assertEqual(normal.weights, [{0: copies}])
                self.assertEqual(normal.stats['barcode_splits'], copies - 1)
                normal.check_d_squared()

    def test_saturated_weights_and_optional_size_skip(self):
        normal = make_connected_ladder(BarcodeScan, 11, 4, rank_cap=3)
        normal._compress([0] * normal.live)
        self.assertEqual(normal.live, 4)
        self.assertEqual(normal.weights, [{0: 3}])
        skipped = make_connected_ladder(BarcodeScan, 11, 4)
        skipped.barcode_max_objects = 43
        skipped._compress([0] * skipped.live)
        self.assertEqual(skipped.live, 44)
        self.assertEqual(skipped.stats['barcode_skipped_size'], 1)

    def test_reject_different_morphism_or_matching(self):
        for kind in ['morphism', 'matching']:
            normal = make_connected_ladder(BarcodeScan, 4, 2)
            if kind == 'morphism':
                normal.out[0][4] = 4
            else:
                normal.mid[0] = normal.algebra.intern(((0, 3), (1, 2)))
            normal._compress([0] * normal.live)
            self.assertEqual(normal.live, 8)
            self.assertEqual(normal.stats['barcode_components'], 0)

    def test_raw_degree_shifts_and_singleton_sharing(self):
        normal = make_connected_ladder(BarcodeScan, 3, 2)
        # All-ones rank-one matrix has one length-two bar and four singleton bars.
        normal.out = [{b: 2 for b in range(3, 6)} if a < 3 else {} for a in range(6)]
        normal.inc = [set() if b < 3 else set(range(3)) for b in range(6)]
        normal.deg = [h + 5 for h in normal.deg]
        normal._compress([0] * normal.live)
        self.assertEqual(normal.live, 3)
        self.assertIn({5: 2, 6: 2}, normal.weights)
        self.assertIn({5: 1}, normal.weights)

    def test_decision_length_caps_do_not_claim_homotopy_equivalence(self):
        for cap in [2, 3]:
            normal = make_connected_ladder(BarcodeScan, 5, 9, rank_cap=3, length_cap=cap)
            normal._compress([0] * normal.live)
            self.assertEqual(normal.live, cap)
            self.assertEqual(normal.weights, [{0: 3}])
            self.assertEqual(normal.stats['barcode_removed_objects'], 5 * (9 - cap))
            self.assertIn('max_weighted_decision_model_objects', normal.stats)
            self.assertNotIn('max_expanded_after_elimination_lower_bound', normal.stats)
            self.assertTrue(normal.stage_history[0]['decision_equivalence_only'])
            normal.check_d_squared()
        with self.assertRaises(ValueError):
            BarcodeScan(length_cap=2)
        with self.assertRaises(ValueError):
            BarcodeScan(rank_cap=3, length_cap=1)

    def test_dense_string_closures_and_sharp_caps(self):
        # Free string I_m as a suffix gives total rank 2*min(l,m).
        for length in range(1, 9):
            for m in range(1, 7):
                def closed(l):
                    return sum(totalized_homology([1] * l, [[1]] * (l - 1),
                                                 [1] * m, [[1]] * (m - 1)).values())
                rank = closed(length)
                self.assertEqual(rank, 2 * min(length, m))
                self.assertEqual(min(3, rank), min(3, closed(min(length, 2))))
        # The simple module k with theta=0 gives rank l. It rules out a
        # universal length-two cap; three is sharp for arbitrary suffixes.
        self.assertNotEqual(min(3, 3), min(3, 2))
        for length in range(1, 12):
            self.assertEqual(min(3, length), min(3, min(length, 3)))
            # Actual scanner closures have even Euler parity. A pair of k's
            # has rank 2*l and supports the sharper length-two cap.
            self.assertEqual(min(3, 2 * length), min(3, 2 * min(length, 2)))


class ScannerTests(unittest.TestCase):
    def test_named_knots_and_capped_decisions(self):
        for name in ['unknot', 'trefoil', 'figure_eight', 'conway', 'kinoshita_terasaka', 'hard_unknot_8']:
            diagram = Diagram.from_json(json.loads((ROOT / 'examples' / (name + '.json')).read_text()))
            ordinary = khovanov_rank(diagram.pd)
            normal = barcode_khovanov_rank(diagram.pd, check_d_squared=True)
            capped = barcode_khovanov_decide(diagram.pd, check_d_squared=True)
            self.assertEqual(normal['rank'], ordinary['rank'])
            self.assertEqual(normal['by_degree'], ordinary['by_degree'])
            self.assertEqual(capped['rank_capped'], min(3, ordinary['rank']))

    def test_random_braid_orders(self):
        rng = random.Random(88299)
        tested = 0
        while tested < 60:
            strands = rng.randrange(2, 6)
            word = [rng.choice([-1, 1]) * rng.randrange(1, strands)
                    for _ in range(rng.randrange(3, 15))]
            try:
                diagram = Diagram.from_braid(strands, word)
            except ValueError:
                continue
            order = list(range(len(word)))
            if tested % 2:
                rng.shuffle(order)
            ordinary = khovanov_rank(diagram.pd, order=order)
            normal = barcode_khovanov_rank(diagram.pd, order=order, check_d_squared=True)
            self.assertEqual(normal['rank'], ordinary['rank'])
            self.assertEqual(normal['by_degree'], ordinary['by_degree'])
            tested += 1


if __name__ == '__main__':
    unittest.main(verbosity=2)
