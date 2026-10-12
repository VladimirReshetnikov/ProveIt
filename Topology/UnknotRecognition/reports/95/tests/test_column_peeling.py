"""Finite independent audits of the full-row cancellation theorem."""

from copy import deepcopy
from functools import lru_cache
from itertools import combinations, permutations, product
from pathlib import Path
import importlib.util
import random
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'code'))

from column_peeling import column_peeling_plan
from column_peeling_verify import (
    verify_column_obstruction, verify_column_peeling_certificate)


def as_counts(matrix):
    return {r: dict(enumerate(row)) for r, row in enumerate(matrix)}


@lru_cache(maxsize=None)
def literal_positive_pivot_completion(matrix):
    """Explore all allowed pivots; no use of leaf criteria or matching."""
    if not matrix:
        return True
    if not matrix[0] or len(matrix) > len(matrix[0]):
        return False
    for r, row in enumerate(matrix):
        for c, value in enumerate(row):
            if value != 1:
                continue
            child = tuple(tuple(min(2, matrix[i][h] + matrix[i][c] * matrix[r][h])
                                for h in range(len(row)) if h != c)
                          for i in range(len(matrix)) if i != r)
            if literal_positive_pivot_completion(child):
                return True
    return False


def a_unit_permanent_minor_exists(matrix):
    if not matrix:
        return True
    rows = len(matrix)
    columns = len(matrix[0])
    for chosen in combinations(range(columns), rows):
        permanent = 0
        for assignment in permutations(chosen):
            term = 1
            for r, c in enumerate(assignment):
                term *= matrix[r][c]
            permanent += term
            if permanent > 1:
                break
        if permanent == 1:
            return True
    return False


class ColumnPeelingTests(unittest.TestCase):
    def test_exhaustive_against_all_positive_pivot_orders(self):
        cases = 0
        for rows, columns, alphabet in (
                (1, 0, range(3)), (1, 3, range(3)),
                (2, 1, range(3)), (2, 3, range(3)),
                (2, 4, range(3)), (3, 3, range(3)),
                (3, 4, range(2))):
            for entries in product(alphabet, repeat=rows * columns):
                matrix = tuple(tuple(entries[r * columns:(r + 1) * columns])
                               for r in range(rows))
                counts = as_counts(matrix)
                result = column_peeling_plan(counts)
                self.assertEqual(result['status'] == 'COMPLETE',
                                 literal_positive_pivot_completion(matrix), matrix)
                self.assertTrue(verify_column_peeling_certificate(
                    counts, result['certificate']), matrix)
                if result['remaining_rows']:
                    self.assertTrue(verify_column_obstruction(
                        counts, result['remaining_rows']), matrix)
                self.assertLessEqual(result['stats']['removal_incidence_visits'],
                                     result['stats']['nonzero_entries'])
                self.assertLessEqual(result['stats']['queue_pushes'], columns)
                cases += 1
        self.assertEqual(cases, 31106)

    def test_matching_minor_criterion_on_random_rectangles(self):
        rng = random.Random(26101219)
        for _ in range(600):
            rows = rng.randrange(5)
            columns = rng.randrange(7)
            matrix = tuple(tuple(rng.randrange(3) for _ in range(columns))
                           for _ in range(rows))
            result = column_peeling_plan(as_counts(matrix))
            self.assertEqual(result['status'] == 'COMPLETE',
                             a_unit_permanent_minor_exists(matrix), matrix)

    def test_pinned_minimum_fill_is_complete_for_the_same_question(self):
        path = Path(__file__).resolve().parents[1] / 'baseline' / 'core_handlebody_7046006.py'
        spec = importlib.util.spec_from_file_location('pinned_core_handlebody', path)
        native = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(native)
        cases = 0
        for rows, columns, alphabet in (
                (2, 3, range(3)), (3, 3, range(3)), (3, 4, range(2))):
            for entries in product(alphabet, repeat=rows * columns):
                counts = {r: {c: entries[r * columns + c] for c in range(columns)}
                          for r in range(rows)}
                old = native.capped_cancellation_plan(counts)
                new = column_peeling_plan(counts)
                self.assertEqual(bool(old['remaining_rows']), bool(new['remaining_rows']))
                if not new['remaining_rows']:
                    self.assertEqual(old['stats']['entry_updates'], 0)
                cases += 1
        self.assertEqual(cases, 24508)

    def test_residual_is_union_of_every_stopping_subset(self):
        for entries in product(range(2), repeat=9):
            matrix = tuple(tuple(entries[3 * r:3 * r + 3]) for r in range(3))
            counts = as_counts(matrix)
            expected = set()
            for mask in range(1, 8):
                subset = [r for r in range(3) if mask >> r & 1]
                # This literal test neither calls the producer nor its checker.
                if all(sum(matrix[r][c] for r in subset) != 1 for c in range(3)):
                    expected.update(subset)
            baseline = column_peeling_plan(counts)['remaining_rows']
            self.assertEqual(set(baseline), expected)
            reversed_source = {r: dict(reversed(list(row.items())))
                               for r, row in reversed(list(counts.items()))}
            self.assertEqual(column_peeling_plan(reversed_source)['remaining_rows'],
                             baseline)

    def test_sparse_labels_huge_counts_and_empty_rows(self):
        r, c = 1 << 256, 1 << 512
        counts = {r: {c: 1, c + 1: 1 << 4096}, r + 1: {c + 1: 3, c + 2: 1}}
        saved = deepcopy(counts)
        result = column_peeling_plan(counts)
        self.assertEqual(result['status'], 'COMPLETE')
        self.assertTrue(verify_column_peeling_certificate(counts, result['certificate']))
        self.assertEqual(counts, saved)
        for source in ({}, {0: {}}, {0: {3: 0}}):
            result = column_peeling_plan(source)
            self.assertEqual(result['status'] == 'COMPLETE', not source)
            self.assertTrue(verify_column_peeling_certificate(source, result['certificate']))

    def test_full_completion_is_not_maximum_partial_cancellation(self):
        counts = {0: {0: 1, 1: 1}, 1: {0: 1, 1: 1}}
        result = column_peeling_plan(counts)
        self.assertEqual(result['cancellations'], [])
        self.assertEqual(result['remaining_rows'], [0, 1])
        self.assertTrue(verify_column_obstruction(counts, [0, 1]))
        # There are four available raw unit pivots; any one of them leaves [2].
        self.assertEqual(min(2, 1 + 1 * 1), 2)

    def test_checker_rejects_tampering_and_incomplete_residual(self):
        counts = {0: {0: 1, 2: 2}, 1: {0: 1, 1: 1}, 2: {3: 2}}
        result = column_peeling_plan(counts)
        certificate = result['certificate']
        self.assertEqual(result['remaining_rows'], [2])
        self.assertTrue(verify_column_peeling_certificate(counts, certificate))
        alterations = []
        bad = deepcopy(certificate); bad['eliminations'].reverse(); alterations.append(bad)
        bad = deepcopy(certificate); bad['residual_rows'] = []; alterations.append(bad)
        bad = deepcopy(certificate); bad['eliminations'][0][1] = True; alterations.append(bad)
        bad = deepcopy(certificate); bad['residual_rows'] = [2, 2]; alterations.append(bad)
        bad = deepcopy(certificate); bad['schema'] = 'claimed-topology'; alterations.append(bad)
        bad = deepcopy(certificate); bad['extra'] = 1; alterations.append(bad)
        bad = deepcopy(certificate); bad['eliminations'].append([2, 3]); bad['residual_rows'] = []
        alterations.append(bad)
        for bad in alterations:
            self.assertFalse(verify_column_peeling_certificate(counts, bad), bad)
        nonmaximal = dict(schema='full-row-column-peeling-v1', eliminations=[],
                          residual_rows=sorted(counts))
        self.assertFalse(verify_column_peeling_certificate(counts, nonmaximal))
        self.assertTrue(verify_column_obstruction(counts, [2]))
        self.assertFalse(verify_column_obstruction(counts, []))
        self.assertFalse(verify_column_obstruction(counts, [0]))

    def test_invalid_sources_are_rejected(self):
        malformed = [[], {True: {}}, {0: []}, {0: {-1: 1}},
                     {0: {True: 1}}, {0: {0: True}}, {0: {0: -1}},
                     {0: {0: 1.0}}, {-1: {0: 1}}]
        certificate = dict(schema='full-row-column-peeling-v1', eliminations=[],
                           residual_rows=[])
        for counts in malformed:
            with self.assertRaises(ValueError):
                column_peeling_plan(counts)
            self.assertFalse(verify_column_peeling_certificate(counts, certificate))

    def test_callback_exceptions_propagate(self):
        class Stop(Exception):
            pass
        def stop():
            raise Stop
        with self.assertRaises(Stop):
            column_peeling_plan({0: {0: 1}}, check=stop)
        with self.assertRaises(Stop):
            verify_column_peeling_certificate({}, {}, check=stop)
        with self.assertRaises(Stop):
            verify_column_obstruction({}, [], check=stop)


if __name__ == '__main__':
    unittest.main()
