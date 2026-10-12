"""Complete raw cancellation against exhaustive schedules and genuine cores."""

from copy import deepcopy
from functools import lru_cache
from itertools import combinations, permutations, product
import json
from pathlib import Path
import random
import unittest
from unittest.mock import patch

from fastunknot.column_cancellation_verify import (
    verify_column_cancellations, verify_raw_cancellation_obstruction)
from fastunknot.core_handlebody import (
    capped_cancellation_plan, column_cancellation_plan, core_handlebody_certificate,
    _forest, _occurrences)
from fastunknot.core_handlebody_verify import verify_core_handlebody_certificate
from fastunknot.normal_parallelity_geometry import _parallelity_geometry
from fastunknot.normal_surface_geometry import _prepare, _coordinates


@lru_cache(None)
def exhaustive_positive_cancellation(matrix):
    """Search every legal saturated pivot; no leaf/matching theorem is used."""
    if not matrix:
        return True
    m, n = len(matrix), len(matrix[0])
    for r in range(m):
        for c in range(n):
            if matrix[r][c] != 1:
                continue
            after = tuple(tuple(min(2, matrix[i][h] + matrix[i][c] * matrix[r][h])
                                for h in range(n) if h != c)
                          for i in range(m) if i != r)
            if exhaustive_positive_cancellation(after):
                return True
    return False


def permanent_one_minor(matrix):
    m, n = len(matrix), len(matrix[0]) if matrix else 0
    for columns in combinations(range(n), m):
        total = 0
        for order in permutations(columns):
            term = 1
            for r, c in enumerate(order):
                term *= matrix[r][c]
            total += term
        if total == 1:
            return True
    return False


class ColumnCancellationTests(unittest.TestCase):
    def test_exhaustive_all_saturated_schedules_on_31096_matrices(self):
        observed = 0
        for m, n, radix in ((1, 3, 3), (2, 3, 3), (2, 4, 3),
                            (3, 3, 3), (3, 4, 2)):
            for entries in product(range(radix), repeat=m * n):
                matrix = tuple(tuple(entries[r * n:(r + 1) * n]) for r in range(m))
                counts = {r: dict(enumerate(row)) for r, row in enumerate(matrix)}
                result = column_cancellation_plan(counts)
                success = not result['remaining_rows']
                self.assertEqual(success, exhaustive_positive_cancellation(matrix), matrix)
                self.assertEqual(success,
                                 not capped_cancellation_plan(counts)['remaining_rows'], matrix)
                self.assertTrue(verify_column_cancellations(
                    counts, result['cancellations'], complete=success))
                if not success:
                    self.assertTrue(verify_raw_cancellation_obstruction(
                        counts, result['remaining_rows']))
                observed += 1
        self.assertEqual(observed, 31096)

    def test_selected_minors_and_canonical_greatest_blocked_set(self):
        rng = random.Random(26101231)
        for _ in range(350):
            m, n = rng.randrange(1, 6), rng.randrange(1, 7)
            matrix = [[rng.randrange(3) for _ in range(n)] for _ in range(m)]
            counts = {r: dict(enumerate(row)) for r, row in enumerate(matrix)}
            result = column_cancellation_plan(counts)
            self.assertEqual(not result['remaining_rows'], permanent_one_minor(matrix))
            greatest = set()
            for bits in range(1, 1 << m):
                selected = [r for r in range(m) if bits >> r & 1]
                if all(sum(matrix[r][c] for r in selected) != 1 for c in range(n)):
                    greatest.update(selected)
            self.assertEqual(set(result['remaining_rows']), greatest)
            row_order = list(counts)
            rng.shuffle(row_order)
            shuffled = {}
            for r in row_order:
                columns = list(counts[r])
                rng.shuffle(columns)
                shuffled[r] = {c: counts[r][c] for c in columns}
            other = column_cancellation_plan(shuffled)
            self.assertEqual(set(other['remaining_rows']), greatest)

    def test_sparse_queue_work_bound_and_long_rectangular_chain(self):
        size = 4000
        counts = {r: {r: 1, r + 1: 1} for r in range(size)}
        result = column_cancellation_plan(counts)
        self.assertEqual(result['remaining_rows'], [])
        self.assertEqual(result['stats']['incidence_visits'], 2 * size)
        self.assertLessEqual(result['stats']['queue_pushes'], size + 1)
        self.assertEqual(result['stats']['entry_updates'], 0)
        self.assertTrue(verify_column_cancellations(counts, result['cancellations']))

    def test_blocked_does_not_mean_no_partial_pivot_or_nonhandlebody(self):
        counts = {0: {0: 1, 1: 1}, 1: {0: 1, 1: 1}}
        column = column_cancellation_plan(counts)
        legacy = capped_cancellation_plan(counts)
        self.assertEqual(column['cancellations'], [])
        self.assertEqual(len(legacy['cancellations']), 1)
        self.assertTrue(verify_raw_cancellation_obstruction(counts, [0, 1]))
        self.assertFalse(verify_raw_cancellation_obstruction(counts, [0]))

    def test_hostile_prefixes_obstructions_and_input_types(self):
        counts = {4: {10: 1, 12: 1}, 6: {12: 1, 18: 1}}
        before = deepcopy(counts)
        good = column_cancellation_plan(counts)
        self.assertEqual(counts, before)
        self.assertTrue(verify_column_cancellations(counts, good['cancellations']))
        for moves in ([[[4, 12], [6, 18]]], [[4, 12], [6, 18]],
                      [[4, 10], [4, 12]], [[4, 10], [6, True]],
                      [[4, 10]], [[4, 10], [6, 10]]):
            self.assertFalse(verify_column_cancellations(counts, moves))
        self.assertTrue(verify_column_cancellations(counts, [[4, 10]], complete=False))
        for rows in ([], [4], [4, 4], [True], [100]):
            self.assertFalse(verify_raw_cancellation_obstruction(counts, rows))
        for bad in ({True: {0: 1}}, {0: {False: 1}}, {0: {0: True}},
                    {0: {0: -1}}, {0: []}, []):
            with self.assertRaises(ValueError):
                column_cancellation_plan(bad)
            self.assertFalse(verify_column_cancellations(bad, []))
        self.assertTrue(verify_column_cancellations({}, []))
        self.assertTrue(verify_raw_cancellation_obstruction({0: {}}, [0]))
        huge = {0: {0: 1 << 16000, 1: 1}, 1: {0: 1}}
        result = column_cancellation_plan(huge)
        self.assertFalse(result['remaining_rows'])
        self.assertTrue(verify_column_cancellations(huge, result['cancellations']))

    def test_all_106_source_cores_and_legacy_capped_replay(self):
        bank = json.loads((Path(__file__).parents[1] /
                           'marked_parallelity_research/corpus.json').read_text())['cases']
        column_cases = 0
        for case in bank:
            prepared = _prepare(case['triangulation'], lambda: None)
            vector = _coordinates(prepared, case['coordinates'], lambda: None)
            core = _parallelity_geometry(prepared, vector, lambda: None)['core']
            result = core_handlebody_certificate(core)
            if core['handles3']:
                self.assertEqual(result['reason'], 'core_has_three_handles')
                continue
            tree, _ = _forest(core, lambda: None)
            counts = _occurrences(core, tree, lambda: None)
            legacy = capped_cancellation_plan(counts)
            self.assertEqual(result['status'] == 'COMPLETE', not legacy['remaining_rows'])
            if result['status'] != 'COMPLETE':
                continue
            proof = result['certificate']
            with patch('fastunknot.core_handlebody.column_cancellation_plan',
                       side_effect=AssertionError('producer used')):
                self.assertTrue(verify_core_handlebody_certificate(core, proof))
            if proof['method'] == 'column_leaf':
                column_cases += 1
                self.assertEqual(proof['schema'], 'normal-core-handlebody-v2')
                old = deepcopy(proof)
                old.update(schema='normal-core-handlebody-v1', method='capped')
                self.assertTrue(verify_core_handlebody_certificate(core, old))
                bad = deepcopy(proof)
                bad['cancellations'].append(bad['cancellations'][0])
                self.assertFalse(verify_core_handlebody_certificate(core, bad))
        self.assertEqual(len(bank), 106)
        self.assertEqual(column_cases, 24)

    def test_callbacks_propagate_even_when_callable_is_false(self):
        class Stop:
            def __bool__(self):
                return False
            def __call__(self):
                raise RuntimeError('cancelled')
        with self.assertRaisesRegex(RuntimeError, 'cancelled'):
            column_cancellation_plan({}, check=Stop())
        with self.assertRaisesRegex(RuntimeError, 'cancelled'):
            verify_column_cancellations({}, [], check=Stop())
        with self.assertRaisesRegex(RuntimeError, 'cancelled'):
            verify_raw_cancellation_obstruction({0: {}}, [0], check=Stop())


if __name__ == '__main__':
    unittest.main()
