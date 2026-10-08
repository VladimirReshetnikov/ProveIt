"""Exact algebraic tests for the research perturbation backend."""
import copy
from collections import Counter
import itertools
import random
import unittest

from fastunknot.diagram import Diagram, DiagramError
from fastunknot.ordering import best_scan_order
from fastunknot.perturbation import (
    Arithmetic, Map, Space, add, identity, install, khovanov_perturbation,
    minimal_model, scalar_contraction, verify_contraction,
)
from fastunknot.planar import Planar
from fastunknot.scan import khovanov_rank
from fastunknot.scan_fast import FastScan


def catalan_matchings(points):
    if not points:
        yield ()
        return
    for j in range(1, len(points), 2):
        for inside in catalan_matchings(points[1:j]):
            for outside in catalan_matchings(points[j + 1:]):
                yield tuple(sorted(((points[0], points[j]),) + inside + outside))


def monomials(value):
    while value:
        low = value & -value
        yield low.bit_length() - 1
        value ^= low


class PerturbationTests(unittest.TestCase):
    def test_grading_on_non_catalan_bipartite_frontiers(self):
        products = 0
        for arcs in range(4):
            alg = Planar(shape_cache=False)
            ids = [alg.intern(tuple(zip(range(arcs), permutation)))
                   for permutation in itertools.permutations(range(arcs, 2 * arcs))]
            for a, b, c in itertools.product(ids, repeat=3):
                ca, cb, cc = (alg.basis(a, b)[1], alg.basis(b, c)[1], alg.basis(a, c)[1])
                for f in range(1 << ca):
                    for g in range(1 << cb):
                        value = alg.compose(a, b, c, 1 << f, 1 << g)
                        degree = 2 * arcs - ca - cb + 2 * (f.bit_count() + g.bit_count())
                        for out in monomials(value):
                            self.assertEqual(arcs - cc + 2 * out.bit_count(), degree)
                        products += 1
        self.assertEqual(products, 3533)

    def test_positive_grading_exhaustive(self):
        products = 0
        for arcs in range(4):
            alg = Planar(shape_cache=False)
            ids = [alg.intern(pairs) for pairs in catalan_matchings(tuple(range(2 * arcs)))]
            for a, b, c in itertools.product(ids, repeat=3):
                ca, cb, cc = (alg.basis(a, b)[1], alg.basis(b, c)[1], alg.basis(a, c)[1])
                for f in range(1 << ca):
                    for g in range(1 << cb):
                        value = alg.compose(a, b, c, 1 << f, 1 << g)
                        degree = 2 * arcs - ca - cb + 2 * (f.bit_count() + g.bit_count())
                        for out in monomials(value):
                            self.assertEqual(arcs - cc + 2 * out.bit_count(), degree)
                            self.assertLessEqual(degree, 2 * arcs)
                        products += 1
        self.assertGreater(products, 1000)

    def test_scalar_contraction_is_an_exact_strong_retraction(self):
        space = Space((0,) * 8, (0, 0, 0, 1, 1, 1, 2, 2))
        # Two consecutive maps, with their composite zero; not already diagonal.
        differential = Map(space, space, [
            {3: 1, 4: 1}, {3: 1, 4: 1}, {4: 1, 5: 1},
            {6: 1}, {6: 1}, {6: 1}, {}, {}])
        d0, inclusion, projection, homotopy, profile = scalar_contraction(space, differential)
        minimal = Map(inclusion.source, inclusion.source,
                      [{} for _ in inclusion.source.matching])
        self.assertTrue(verify_contraction(d0, minimal, inclusion, projection, homotopy,
                                          Arithmetic(Planar(shape_cache=False))))
        self.assertEqual(len(minimal.source), 2)
        self.assertEqual(sum(p['minimal_objects'] for p in profile), 2)

    def test_scanner_prefixes_against_scalar_cancellation(self):
        rng = random.Random(756)
        cases = [(3, [1, 2] * 4), (3, [1, -2] * 4),
                 (4, [1, 2, 3, -2, -1, 2, 3, 2, 1])]
        accepted = 0
        for strands in (2, 3, 4):
            for _ in range(12):
                word = [rng.choice((-1, 1)) * rng.randrange(1, strands)
                        for _ in range(rng.randrange(2, 8))]
                cases.append((strands, word))
        for strands, word in cases:
            try:
                diagram = Diagram.from_braid(strands, word)
            except DiagramError:
                continue
            order = list(range(diagram.crossings))
            rng.shuffle(order)
            scan = FastScan(shape_cache=False)
            for index in order:
                scan.add_crossing(diagram.pd[index], reduce_now=False)
                scalar = copy.deepcopy(scan)
                scalar.eliminate()
                model = minimal_model(scan, certificate=True)
                self.assertTrue(model['certified'])
                expected = Counter((m, scalar.deg[i]) for i, m in enumerate(scalar.mid)
                                   if m is not None)
                actual = Counter(zip(model['space'].matching, model['space'].degree))
                self.assertEqual(actual, expected)
                install(scan, model)
            self.assertEqual(scan.ranks_by_degree(), khovanov_rank(diagram.pd)['by_degree'])
            accepted += 1
        self.assertGreaterEqual(accepted, 10)

    def test_nonzero_perturbation_depth(self):
        diagram = Diagram.from_braid(3, [1, 2] * 4)
        result = khovanov_perturbation(diagram.pd, certificate=True)
        self.assertGreaterEqual(result['stats']['max_perturbation_depth'], 2)
        self.assertEqual(result['by_degree'], khovanov_rank(diagram.pd)['by_degree'])

    def test_rejects_noncomplex(self):
        scan = FastScan(shape_cache=False)
        scan.mid, scan.deg = [0, 0, 0], [0, 1, 2]
        scan.out, scan.inc, scan.live = [{1: 1}, {2: 1}, {}], [set(), {0}, {1}], 3
        with self.assertRaises(ArithmeticError):
            minimal_model(scan, certificate=True)

    def test_certificate_detects_mutation(self):
        diagram = Diagram.from_braid(2, [1])
        scan = FastScan(shape_cache=False)
        scan.add_crossing(diagram.pd[0], reduce_now=False)
        model = minimal_model(scan, certificate=True)
        from fastunknot.perturbation import snapshot
        _, original = snapshot(scan)
        changed = copy.deepcopy(model['projection'])
        for row in changed.rows:
            if row:
                row.clear()
                break
        with self.assertRaises(ArithmeticError):
            verify_contraction(original, model['differential'], model['inclusion'], changed,
                               model['homotopy'], Arithmetic(scan.algebra))


if __name__ == '__main__':
    unittest.main()
