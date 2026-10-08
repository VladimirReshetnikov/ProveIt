"""Independent checks of dense composition, its plan edge cases, and scanner use."""
from __future__ import annotations

import random
import unittest

from fastunknot.dense_compose import (AdaptivePlanar, FastCompositionPlan, compose_plan_fast,
                          squarefree_product, _sparse_compose)
from fastunknot.planar import Planar
from fastunknot.scan_fast import FastScan
from fastunknot.diagram import Diagram


def scalar_reference(components, f, g, left_vars, right_vars):
    """Direct surface rule, independent of production evaluate and transforms."""
    if components is None:
        return 0
    result = set()
    for left in range(1 << left_vars):
        if not (f >> left) & 1:
            continue
        for right in range(1 << right_vars):
            if not (g >> right) & 1:
                continue
            terms = {0}
            for lm, rm, boundary, extra, *_ in components:
                dot_count = (left & lm).bit_count() + (right & rm).bit_count() + extra
                if dot_count > 1 or (not boundary and dot_count != 1):
                    terms = set()
                    break
                if dot_count:
                    choices = [boundary]
                else:
                    choices = [boundary ^ (1 << bit) for bit in range(boundary.bit_length())
                               if (boundary >> bit) & 1]
                next_terms = set()
                for term in terms:
                    for choice in choices:
                        monomial = term | choice
                        if monomial in next_terms:
                            next_terms.remove(monomial)
                        else:
                            next_terms.add(monomial)
                terms = next_terms
            result.symmetric_difference_update(terms)
    return sum(1 << mask for mask in result)


def noncrossing_matchings(points):
    if not points:
        yield ()
        return
    for mate in range(1, len(points), 2):
        for inside in noncrossing_matchings(points[1:mate]):
            for outside in noncrossing_matchings(points[mate + 1:]):
                yield tuple(sorted(((points[0], points[mate]),) + inside + outside))


class ProductTests(unittest.TestCase):
    def test_exhaustive_small_algebras(self):
        for variables in range(3):
            components = [(1 << i, 1 << i, 1 << i, 0) for i in range(variables)]
            for f in range(1 << (1 << variables)):
                for g in range(1 << (1 << variables)):
                    self.assertEqual(squarefree_product(f, g, variables),
                                     scalar_reference(components, f, g, variables, variables))

    def test_random_dense_and_sparse(self):
        rng = random.Random(2601007)
        for variables in range(3, 9):
            components = [(1 << i, 1 << i, 1 << i, 0) for i in range(variables)]
            for _ in range(20):
                f, g = rng.getrandbits(1 << variables), rng.getrandbits(1 << variables)
                self.assertEqual(squarefree_product(f, g, variables),
                                 scalar_reference(components, f, g, variables, variables))
                self.assertEqual(squarefree_product(f, f, variables), f & 1)

    def test_nilpotence_requires_rank(self):
        self.assertEqual(squarefree_product(2, 2, 1), 0)
        self.assertEqual(squarefree_product(3, 3, 1), 1)
        self.assertEqual(squarefree_product(2, 4, 2), 8)

    def test_homogeneous_fast_path(self):
        rng = random.Random(2901008)
        for variables in range(1, 10):
            components = [(1 << i, 1 << i, 1 << i, 0) for i in range(variables)]
            for _ in range(30):
                p, q = rng.randrange(variables + 1), rng.randrange(variables + 1)
                f = sum(1 << mask for mask in range(1 << variables)
                        if mask.bit_count() == p and rng.randrange(2))
                g = sum(1 << mask for mask in range(1 << variables)
                        if mask.bit_count() == q and rng.randrange(2))
                self.assertEqual(squarefree_product(f, g, variables),
                                 scalar_reference(components, f, g, variables, variables))


class GeneralPlanTests(unittest.TestCase):
    def test_closed_extra_and_positive_genus(self):
        # A closed undotted sphere is zero; a closed singly dotted sphere is 1.
        self.assertEqual(compose_plan_fast([(0, 0, 0, 0)], 1, 1, 0, 0, 0), 0)
        self.assertEqual(compose_plan_fast([(0, 0, 0, 1)], 1, 1, 0, 0, 0), 1)
        self.assertEqual(compose_plan_fast([(0, 0, 0, 2)], 1, 1, 0, 0, 0), 0)
        self.assertEqual(compose_plan_fast(None, 3, 3, 1, 1, 0), 0)
        # Comultiplication and trace followed by a disjoint cup.
        self.assertEqual(compose_plan_fast([(1, 0, 3, 0)], 1, 1, 1, 0, 2), 6)
        self.assertEqual(compose_plan_fast([(1, 0, 3, 0)], 2, 1, 1, 0, 2), 8)
        self.assertEqual(compose_plan_fast([(1, 0, 0, 0), (0, 0, 1, 0)],
                                          2, 1, 1, 0, 1), 1)

    def test_random_general_plans(self):
        rng = random.Random(2701007)
        for _ in range(700):
            counts = [rng.randrange(6) for _ in range(3)]
            r = rng.randrange(1, 7)
            components = [[0, 0, 0, rng.choice((0, 0, 0, 1, 2))] for _ in range(r)]
            for side, count in enumerate(counts):
                for variable in range(count):
                    components[rng.randrange(r)][side] |= 1 << variable
            f = rng.getrandbits(1 << counts[0])
            g = rng.getrandbits(1 << counts[1])
            self.assertEqual(compose_plan_fast(components, f, g, *counts),
                             scalar_reference(components, f, g, *counts[:2]))
            self.assertEqual(_sparse_compose(components, f, g, *counts),
                             scalar_reference(components, f, g, *counts[:2]))

    def test_invalid_plans_fail(self):
        with self.assertRaises(ValueError):
            FastCompositionPlan([(1, 1, 1, 0), (1, 0, 0, 0)], 1, 1, 1)
        with self.assertRaises(ValueError):
            FastCompositionPlan([], 1, 0, 0)
        with self.assertRaises(ValueError):
            FastCompositionPlan([(1, 1, 1, -1)], 1, 1, 1)
        with self.assertRaises(ValueError):
            squarefree_product(4, 1, 1)


class MatchingPlanTests(unittest.TestCase):
    def test_all_small_matching_triples(self):
        rng = random.Random(2801007)
        checked = 0
        for boundary in (0, 2, 4, 6, 8):
            algebra = Planar(shape_cache=False)
            ids = [algebra.intern(m) for m in noncrossing_matchings(tuple(range(boundary)))]
            for a in ids:
                for b in ids:
                    for c in ids:
                        raw = algebra.compose_plan(a, b, c)
                        counts = [algebra.basis(a, b)[1], algebra.basis(b, c)[1],
                                  algebra.basis(a, c)[1]]
                        components = None if raw is None else raw[0]
                        if components is not None:
                            self.assertLessEqual(len(components), min(counts[:2]))
                            self.assertTrue(all(component[0] and component[1]
                                                for component in components))
                        compiled = FastCompositionPlan(components, *counts)
                        for _ in range(3):
                            f, g = rng.getrandbits(1 << counts[0]), rng.getrandbits(1 << counts[1])
                            expected = scalar_reference(components, f, g, *counts[:2])
                            self.assertEqual(compiled.apply(f, g), expected)
                            self.assertEqual(algebra.compose(a, b, c, f, g), expected)
                            checked += 1
        self.assertEqual(checked, 8637)

    def test_adapter_and_scanner(self):
        rng = random.Random(2901007)
        fixtures = [([1, 1, 1], 2), ([1, -2, 1, -2], 3),
                    ([1, 2] * 5, 3), ([1, -2, 3] * 3, 4)]
        for word, strands in fixtures:
            diagram = Diagram.from_braid(strands, word)
            reference = FastScan()
            dense = FastScan()
            dense.algebra = AdaptivePlanar(force_dense=True)
            adaptive = FastScan()
            adaptive.algebra = AdaptivePlanar()
            order = list(range(len(diagram.pd)))
            rng.shuffle(order)
            for crossing in order:
                reference.add_crossing(tuple(diagram.pd[crossing]), reduce_now=False)
                dense.add_crossing(tuple(diagram.pd[crossing]), reduce_now=False)
                adaptive.add_crossing(tuple(diagram.pd[crossing]), reduce_now=False)
                for candidate in (dense, adaptive):
                    self.assertEqual(candidate.mid, reference.mid)
                    self.assertEqual(candidate.deg, reference.deg)
                    self.assertEqual(candidate.out, reference.out)
                    candidate.check_d_squared()
                reference.eliminate()
                dense.eliminate()
                adaptive.eliminate()
                dense.check_d_squared()
                adaptive.check_d_squared()
            self.assertEqual(dense.ranks_by_degree(), reference.ranks_by_degree())
            self.assertEqual(adaptive.ranks_by_degree(), reference.ranks_by_degree())

    def test_dense_transfers_at_actual_scan_stages(self):
        rng = random.Random(3001007)
        comparisons = 0
        for strands, word in ((2, [1] * 5), (3, [1, -2] * 4),
                              (4, [1, -2, 3] * 3)):
            diagram = Diagram.from_braid(strands, word)
            scan = FastScan()
            order = list(range(len(diagram.pd)))
            rng.shuffle(order)
            for crossing in order:
                source_pairs = sorted({scan.algebra.pairs[ma] for ma in scan.mid if ma is not None})
                rng.shuffle(source_pairs)
                source_pairs = source_pairs[:6]
                ordinary = Planar(shape_cache=False)
                dense = AdaptivePlanar(shape_cache=False, force_dense=True)
                slots = tuple(diagram.pd[crossing])
                ordinary.stage(scan.points, slots)
                dense.stage(scan.points, slots)
                for pairs_a in source_pairs:
                    for pairs_b in source_pairs:
                        a, b = ordinary.intern(pairs_a), ordinary.intern(pairs_b)
                        da, db = dense.intern(pairs_a), dense.intern(pairs_b)
                        variables = ordinary.basis(a, b)[1]
                        f = rng.getrandbits(1 << variables)
                        for source_smoothing in range(2):
                            for target_smoothing in range(2):
                                self.assertEqual(dense.transfer(da, db, f, source_smoothing,
                                                                target_smoothing),
                                                 ordinary.transfer(a, b, f, source_smoothing,
                                                                   target_smoothing))
                                comparisons += 1
                scan.add_crossing(slots)
        self.assertGreater(comparisons, 1000)

    def test_transfer_threshold_and_two_closed_circles(self):
        points = frozenset(range(12))
        pairs = tuple((i, i + 1) for i in range(0, 12, 2))
        for slots in ((12, 13, 14, 15), (12, 12, 13, 13), (0, 1, 2, 3)):
            ordinary = Planar(shape_cache=False)
            adaptive = AdaptivePlanar(shape_cache=False)
            ordinary.stage(points, slots)
            adaptive.stage(points, slots)
            a, da = ordinary.intern(pairs), adaptive.intern(pairs)
            for support in (32, 33):
                f = (1 << support) - 1
                for source in range(2):
                    for target in range(2):
                        self.assertEqual(adaptive.transfer(da, da, f, source, target),
                                         ordinary.transfer(a, a, f, source, target))
            self.assertEqual(adaptive.sparse_transfer_calls, 4)
            self.assertEqual(adaptive.dense_transfer_calls, 4)
            if slots == (12, 12, 13, 13):
                self.assertEqual(ordinary.glue(a, 0)[1], 2)


if __name__ == "__main__":
    unittest.main(verbosity=2)
