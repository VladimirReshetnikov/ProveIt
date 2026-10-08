"""Independent component, topology, and compatibility checks for interlace."""
from collections import Counter
from pathlib import Path
import sys
import unittest

FAST_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(FAST_ROOT))

from fastunknot.diagram import Diagram, DiagramError
from fastunknot.factor import visible_factors
from fastunknot.interlace import (interlacement_components,
                                  verify_interlacement_certificate,
                                  visible_factors_interlacement)


def words(n):
    counts, prefix = [0] * n, []

    def visit(opened):
        if len(prefix) == 2 * n:
            yield tuple(prefix)
            return
        for x in range(opened):
            if counts[x] == 1:
                counts[x] = 2
                prefix.append(x)
                yield from visit(opened)
                prefix.pop()
                counts[x] = 1
        if opened < n:
            counts[opened] = 1
            prefix.append(opened)
            yield from visit(opened + 1)
            prefix.pop()
            counts[opened] = 0

    yield from visit(0)


def explicit_components(word):
    n = len(word) // 2
    positions = [[] for _ in range(n)]
    for i, x in enumerate(word):
        positions[x].append(i)
    graph = [set() for _ in range(n)]
    for x in range(n):
        a, b = positions[x]
        for y in range(x):
            c, d = positions[y]
            if a < c < b < d or c < a < d < b:
                graph[x].add(y)
                graph[y].add(x)
    unseen, components = set(range(n)), set()
    while unseen:
        pending, component = [next(iter(unseen))], set()
        while pending:
            x = pending.pop()
            if x in component:
                continue
            component.add(x)
            pending.extend(graph[x] - component)
        unseen.difference_update(component)
        components.add(frozenset(component))
    return components


def word_pd(word, mask):
    n = len(word) // 2
    rows, seen = [[-1] * 4 for _ in range(n)], set()
    for i, x in enumerate(word):
        slot = (3 if mask & (1 << x) else 1) if x in seen else 0
        seen.add(x)
        rows[x][slot] = i
        rows[x][(slot + 2) % 4] = (i + 1) % (2 * n)
    return Diagram.from_pd(rows)


def pd_key(diagram):
    labels = {}
    return tuple(tuple(labels.setdefault(e, len(labels)) for e in row)
                 for row in diagram.pd)


def trefoil_sum(k):
    base = Diagram.from_braid(2, [1, 1, 1])
    rows = [[-1] * 4 for _ in range(3 * k)]
    for block in range(k):
        for i, dart in enumerate(base.traversal()):
            x, slot = divmod(dart, 4)
            position = 6 * block + i
            rows[3 * block + x][slot] = position
            rows[3 * block + x][(slot + 2) % 4] = (position + 1) % (6 * k)
    return Diagram.from_pd(rows)


class InterlacementTests(unittest.TestCase):
    def assert_factorization(self, diagram):
        before = diagram.pd
        old, cuts = visible_factors(diagram)
        factors, certificate = visible_factors_interlacement(diagram)
        direct, _ = visible_factors_interlacement(diagram, validate=False)
        self.assertEqual(Counter(map(pd_key, old)), Counter(map(pd_key, factors)))
        self.assertEqual([pd_key(d) for d in direct], [pd_key(d) for d in factors])
        self.assertEqual(sum(d.crossings for d in factors), diagram.crossings)
        self.assertEqual(len(cuts), max(0, len(factors) - 1))
        self.assertTrue(verify_interlacement_certificate(
            [dart // 4 for dart in diagram.traversal()], certificate))
        self.assertEqual(diagram.pd, before)
        return factors, certificate

    def test_empty_and_single_crossing(self):
        for diagram in (Diagram.from_pd([]), Diagram.from_braid(2, [1])):
            factors, _ = self.assert_factorization(diagram)
            self.assertIs(factors[0], diagram)

    def test_all_abstract_words_through_six_chords(self):
        checked = 0
        for n in range(7):
            for word in words(n):
                components, forest = interlacement_components(word)
                self.assertEqual(set(map(frozenset, components)), explicit_components(word))
                self.assertTrue(verify_interlacement_certificate(word, {
                    "crossing_components": components, "interlacement_forest": forest}))
                checked += 1
        self.assertEqual(checked, 11465)

    def test_all_spherical_rotation_choices_through_four_crossings(self):
        spherical = 0
        for n in range(5):
            for word in words(n):
                for mask in range(1 << n):
                    try:
                        diagram = word_pd(word, mask)
                    except DiagramError:
                        continue
                    self.assert_factorization(diagram)
                    spherical += 1
        self.assertEqual(spherical, 313)

    def test_dense_circle_graph_has_sparse_certificate(self):
        n = 2000
        word = tuple(range(n)) * 2
        components, forest = interlacement_components(word)
        self.assertEqual(len(components), 1)
        self.assertEqual(len(forest), n - 1)
        self.assertTrue(verify_interlacement_certificate(word, {
            "crossing_components": components, "interlacement_forest": forest}))

    def test_cyclic_sum_exposes_baseline_quadratic_work(self):
        for k in (1, 2, 4, 8, 16):
            diagram = trefoil_sum(k)
            factors, _ = self.assert_factorization(diagram)
            self.assertEqual([d.crossings for d in factors], [3] * k)
            _, cuts = visible_factors(diagram)
            work = sum(sum(cut["crossings"]) for cut in cuts)
            self.assertEqual(work, 3 * (k * (k + 1) // 2 - 1))

    def test_crossing_rotation_and_under_over_data(self):
        diagram = trefoil_sum(4)
        rows = []
        for i, row in enumerate(reversed(diagram.pd)):
            # Odd cyclic shifts exchange under and over without changing the
            # spherical rotation; even shifts change the traversal's origin.
            shift = i % 4
            rows.append(row[shift:] + row[:shift])
        self.assert_factorization(Diagram.from_pd(rows))

    def test_certificate_tampering_is_rejected(self):
        word = (0, 1, 2, 0, 1, 2)
        bad = [
            {"crossing_components": [[0], [1], [2]], "interlacement_forest": []},
            {"crossing_components": [[0, 1, 2]],
             "interlacement_forest": [[0, 1], [0, 1]]},
            {"crossing_components": [[0, 1], [1, 2]],
             "interlacement_forest": [[0, 1]]},
            {"crossing_components": [[0, 1]], "interlacement_forest": [[0, 1]]},
        ]
        for certificate in bad:
            with self.assertRaises(ValueError):
                verify_interlacement_certificate(word, certificate)
        with self.assertRaises(ValueError):
            verify_interlacement_certificate((0, 0, 1, 1), {
                "crossing_components": [[0, 1]], "interlacement_forest": [[0, 1]]})

    def test_malformed_double_occurrence_words(self):
        for word in ((0,), (0, 1), (0, 0, 0, 1), (-1, -1), (True, True)):
            with self.assertRaises(ValueError):
                interlacement_components(word)

    def test_cancellation_callback(self):
        class Cancelled(Exception):
            pass

        def check():
            raise Cancelled()

        with self.assertRaises(Cancelled):
            visible_factors_interlacement(trefoil_sum(2), check)


if __name__ == "__main__":
    unittest.main()

