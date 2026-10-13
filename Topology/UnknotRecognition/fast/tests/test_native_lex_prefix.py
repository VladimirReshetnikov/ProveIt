"""Exact default pivot rule, caps and reentrant callbacks; bounded controls."""
from copy import deepcopy
from fractions import Fraction as Q
import inspect
from itertools import product
import json
from math import gcd
from pathlib import Path
import unittest
from unittest.mock import patch

from fastunknot import exact_lp
from fastunknot import normal_euler_tree as tree
from fastunknot.normal_euler_transversal import search_euler_transversal
from fastunknot.normal_euler_tree_verify import verify_euler_branch_tree
from fastunknot.normal_crushing import crush_normal_ray
from fastunknot.normal_crushing_verify import verify_normal_crushing
from normal_orbit_research.fixtures import layered_torus
from tests.test_polynomial_exact_lp import normalized_vertices


class CallerStop(BaseException):
    pass


def tuple_leaving(candidates, tableau, rhs, column, n, check):
    """Literal mathematical reference, independent of integer comparator."""
    def key(i):
        check()
        return (rhs[i]/tableau[i][column],
                *(tableau[i][j]/tableau[i][column]
                  for j in range(n, n+len(tableau))))
    return min(candidates, key=key)


def inverse_point(square, rhs):
    """Small independent Gauss-Jordan basis replay, never solver elimination."""
    rows = [[Q(x) for x in row]+[Q(b)] for row, b in zip(square, rhs)]
    for j in range(len(rows)):
        pivot = next((i for i in range(j, len(rows)) if rows[i][j]), None)
        if pivot is None:
            raise AssertionError('returned slack basis is singular')
        rows[j], rows[pivot] = rows[pivot], rows[j]
        divisor = rows[j][j]
        rows[j] = [x/divisor for x in rows[j]]
        for i in range(len(rows)):
            if i != j:
                factor = rows[i][j]
                rows[i] = [x-factor*y for x, y in zip(rows[i], rows[j])]
    return [row[-1] for row in rows]


def helper_depth():
    frame, count = inspect.currentframe().f_back, 0
    while frame is not None:
        count += frame.f_code.co_name == '_solve_prepared_kernel'
        frame = frame.f_back
    return count


class NativeLexPrefixTests(unittest.TestCase):
    def assert_replay(self, matrix, objective, result):
        matrix = [[Q(x) for x in row] for row in matrix]
        objective = list(map(Q, objective))
        if result['status'] == 'INCONCLUSIVE':
            self.assertTrue(set(result).isdisjoint({'x', 'y', 'basis', 'primitive_x'}))
            return
        vertices = normalized_vertices(matrix, len(objective))
        positive = any(sum(c*x for c, x in zip(objective, point)) > 0
                       for point in vertices)
        self.assertEqual(result['status'], 'POSITIVE' if positive else 'NONPOSITIVE')
        if not positive:
            dual = [Q(*x) for x in result['y']]
            self.assertEqual(len(dual), len(matrix))
            for j, c in enumerate(objective):
                self.assertGreaterEqual(sum(row[j]*y for row, y in zip(matrix, dual)), c)
            return
        point = tuple(Q(*x) for x in result['x'])
        self.assertIn(point, vertices)  # Independent Leibniz/Cramer support oracle.
        self.assertEqual(sum(point), 1)
        self.assertEqual(sum(c*x for c, x in zip(objective, point)), Q(*result['objective']))
        ray = result['primitive_x']
        self.assertTrue(all(type(x) is int and x >= 0 for x in ray))
        self.assertEqual(gcd(*ray), 1)
        self.assertEqual(tuple(Q(x, sum(ray)) for x in ray), point)
        retained = [matrix[i] for i in result['equation_rows']]
        inequalities = retained+[[-a for a in row] for row in retained]+[[Q(1)]*len(point)]
        m, n = len(inequalities), len(point)
        basis = result['basis']
        self.assertEqual(len(basis), m)
        self.assertEqual(len(set(basis)), m)
        self.assertTrue(all(type(j) is int and 0 <= j < n+m for j in basis))
        square = [[row[j] if j < n else Q(j-n == i) for j in basis]
                  for i, row in enumerate(inequalities)]
        basic = inverse_point(square, [Q(0)]*(m-1)+[Q(1)])
        self.assertTrue(all(x >= 0 for x in basic))
        full = [Q(0)]*(n+m)
        for j, x in zip(basis, basic):
            full[j] = x
        self.assertEqual(tuple(full[:n]), point)

    @staticmethod
    def entry(kind, matrix, objective, **options):
        if kind == 'public':
            return exact_lp.solve_nonnegative_kernel(matrix, objective, **options)
        reduce_rows = options.pop('reduce_rows', True)
        prepared = exact_lp._prepare_kernel_matrix(matrix, len(objective),
            reduce_rows=reduce_rows, check=options.get('check', lambda: None))
        return exact_lp._solve_prepared_nonnegative_kernel(prepared, objective, **options)

    def test_entering_exact_maximum_ties_and_no_positive_cost(self):
        cases = [([], None), ([0, -1], None), ([1, 5, 5, 3], 1),
                 ([Q(1, 3), Q(2, 5), Q(4, 10)], 1),
                 ([2**1024, 2**1024+1, -(2**2048)], 1)]
        for values, expected in cases:
            calls = []
            self.assertEqual(exact_lp._dantzig_entering(list(map(Q, values)),
                lambda: calls.append(None)), expected)
            self.assertEqual(len(calls), len(values))

    def test_default_dispatch_uses_largest_cost_and_bland_keeps_first(self):
        for entry in ('public', 'prepared'):
            default = self.entry(entry, [], [1, 3, 3])
            bland = self.entry(entry, [], [1, 3, 3], policy='bland')
            self.assertEqual(default['primitive_x'], [0, 1, 0])
            self.assertEqual(bland['primitive_x'], [1, 0, 0])
            self.assertEqual(default['stats']['pivots'], 1)
            self.assertEqual(bland['stats']['pivots'], 1)
            self.assert_replay([], [1, 3, 3], default)
            self.assert_replay([], [1, 3, 3], bland)

    def test_lazy_order_equals_full_tuple_at_every_component(self):
        # Five original slack columns, all of which can be decisive. These
        # helper-only rows need not form an LP; genuine tableaux are below.
        m, n = 5, 1
        for position, sign, order in product(range(m+1), (-1, 1), ([0, 1], [1, 0])):
            keys = [[Q(0)]*(m+1), [Q(0)]*(m+1)]
            keys[1][position] = Q(sign, 2**257+1)
            coefficients = (Q(2, 7), Q(3, 11))
            tableau = [[Q(0)]*(n+m) for _ in range(m)]
            rhs = [Q(0)]*m
            for i, a in enumerate(coefficients):
                tableau[i][0] = a
                rhs[i] = a*keys[i][0]
                tableau[i][n:] = [a*x for x in keys[i][1:]]
            expected = tuple_leaving(order, tableau, rhs, 0, n, lambda: None)
            actual = exact_lp._lexicographic_leaving(order, tableau, rhs, 0, n, lambda: None)
            self.assertEqual(actual, expected)
        # Equal artificial keys preserve first candidate; valid B^-1 rows
        # cannot have equal complete keys, but min's stable behavior is exact.
        tableau = [[Q(2), Q(0), Q(0)], [Q(3), Q(0), Q(0)]]
        for order in ([0, 1], [1, 0]):
            self.assertEqual(exact_lp._lexicographic_leaving(order, tableau,
                [Q(0), Q(0)], 0, 1, lambda: None), order[0])
        # Unequal positive divisors reverse the unscaled RHS ordering.
        tableau = [[Q(2), Q(-3), Q(1)], [Q(7), Q(4), Q(-2)]]
        self.assertEqual(exact_lp._lexicographic_leaving([0, 1], tableau,
            [Q(1), Q(2)], 0, 1, lambda: None), 1)

    def test_selector_cancellation_including_final_slack_comparison(self):
        tableau = [[Q(1), Q(0), Q(0)], [Q(2), Q(0), Q(-1)]]
        actions = [lambda check: exact_lp._dantzig_entering([Q(1), Q(2), Q(2)], check),
            lambda check: exact_lp._lexicographic_leaving([0, 1], tableau,
                [Q(0), Q(0)], 0, 1, check)]
        for action in actions:
            count = [0]
            def record():
                count[0] += 1
            action(record)
            for stop in range(1, count[0]+1):
                seen, error = [0], ValueError('selector') if stop % 2 else CallerStop('selector')
                def cancel():
                    seen[0] += 1
                    if seen[0] == stop:
                        raise error
                with self.assertRaises(BaseException) as caught:
                    action(cancel)
                self.assertIs(caught.exception, error)

    def test_genuine_zero_rhs_degeneracy_keeps_basic_slack_columns(self):
        matrix, cost = [[1, -1], [2, -2], [0, 0]], [1, 0]
        original = exact_lp._lexicographic_leaving
        selected = []
        def observed(candidates, tableau, rhs, column, n, check):
            row = original(candidates, tableau, rhs, column, n, check)
            if not selected:
                self.assertEqual(column, 0)
                self.assertEqual(candidates, [0, 1, 6])
                self.assertEqual(rhs[:6], [Q(0)]*6)
                self.assertEqual([line[n:] for line in tableau],
                    [[Q(i == j) for j in range(7)] for i in range(7)])
                self.assertEqual(row, 1)  # Bland chooses row 0 at this pivot.
            selected.append(row)
            return row
        with patch.object(exact_lp, '_lexicographic_leaving', side_effect=observed):
            result = exact_lp.solve_nonnegative_kernel(matrix, cost, reduce_rows=False)
        self.assertTrue(selected)
        self.assert_replay(matrix, cost, result)

    def test_lazy_and_tuple_rules_return_identical_complete_results(self):
        cases = [([], []), ([[], []], []), ([], [1, 2, 2]),
            ([[1, -1], [2, -2], [0, 0]], [1, 0]),
            ([[1, -1], [2, -2], [0, 0]], [1, -2]),
            ([[Q(1, 3), Q(-2, 5)]], [Q(2, 7), Q(1, 11)]),
            ([[1, -(2**1024+1)]], [1, 0]), ([[1, 1, -1]], [1, 1, 0])]
        for matrix, cost in cases:
            for reduce_rows in (True, False):
                for options in ({}, dict(max_pivots=0), dict(max_pivots=1)):
                    with self.subTest(matrix=matrix, cost=cost, reduce_rows=reduce_rows, options=options):
                        actual = exact_lp.solve_nonnegative_kernel(matrix, cost,
                            reduce_rows=reduce_rows, **options)
                        with patch.object(exact_lp, '_lexicographic_leaving', tuple_leaving):
                            expected = exact_lp.solve_nonnegative_kernel(matrix, cost,
                                reduce_rows=reduce_rows, **options)
                        self.assertEqual(actual, expected)
                        self.assert_replay(matrix, cost, actual)

    def test_explicit_bland_matches_retained_prechange_results(self):
        fixture = json.loads((Path(__file__).parent/'fixtures/lex_bland_controls.json').read_text())
        self.assertEqual(fixture['schema'], 'native-lex-legacy-controls-v1')
        self.assertEqual(len(fixture['records']), 5)
        with patch.object(exact_lp, '_dantzig_entering', side_effect=AssertionError('Bland called Dantzig')), \
             patch.object(exact_lp, '_lexicographic_leaving', side_effect=AssertionError('Bland called lex')):
            for record in fixture['records']:
                for entry in ('public', 'prepared'):
                    result = self.entry(entry, record['matrix'], record['objective'],
                        policy='bland', **record['options'])
                    self.assertEqual(result, record['result'])
                    self.assert_replay(record['matrix'], record['objective'], result)

    def test_prepared_reuse_is_exact_and_returned_fields_are_fresh(self):
        matrix = [[Q(1, 2), -1], [1, -2], [0, 0]]
        for reduce_rows in (True, False):
            prepared = exact_lp._prepare_kernel_matrix(matrix, 2, reduce_rows=reduce_rows)
            original = deepcopy(prepared)
            for policy, objective in product(('polynomial', 'bland'), ([1, 0], [1, -3], [0, 0])):
                actual = exact_lp._solve_prepared_nonnegative_kernel(prepared, objective, policy=policy)
                fresh = exact_lp.solve_nonnegative_kernel(matrix, objective,
                    reduce_rows=reduce_rows, policy=policy)
                self.assertEqual(actual, fresh)
                self.assert_replay(matrix, objective, actual)
                actual['equation_rows'].clear()
                actual['stats']['pivots'] = -100
                if 'basis' in actual:
                    actual['basis'].clear()
                    actual['x'][0][0] += 100
                if 'y' in actual:
                    actual['y'][0][0] += 100
                self.assertEqual(exact_lp._solve_prepared_nonnegative_kernel(
                    prepared, objective, policy=policy), fresh)
                self.assertEqual(prepared, original)

    def test_terminal_checks_precede_hard_cap_and_hard_cap_blocks_fallback(self):
        matrix, cost = [[1, 1, -1]], [1, 1, 0]
        full = exact_lp.solve_nonnegative_kernel(matrix, cost)
        pivots = full['stats']['pivots']
        self.assertGreater(pivots, 0)
        self.assertEqual(full['stats']['fallback_used'], 0)
        for entry in ('public', 'prepared'):
            self.assertEqual(self.entry(entry, matrix, cost, max_pivots=pivots), full)
            with patch.object(exact_lp, '_ellipsoid_kernel', side_effect=AssertionError('hard cap fallback')):
                for options in (dict(max_pivots=pivots-1), dict(max_pivots=0),
                                dict(max_pivots=0, fast_path_pivots=0)):
                    partial = self.entry(entry, matrix, cost, **options)
                    self.assertEqual(partial['status'], 'INCONCLUSIVE')
                    self.assertEqual(partial['stats']['fallback_used'], 0)
                    self.assert_replay(matrix, cost, partial)
                zero = self.entry(entry, [[1]], [-1], max_pivots=0)
                self.assertEqual(zero['status'], 'NONPOSITIVE')
                self.assertEqual(zero['stats']['pivots'], 0)

    def test_zero_internal_prefix_uses_same_fallback_and_separate_caps(self):
        matrix = [[1, -1]]
        for cost in ([1, 0], [1, -2]):
            with patch.object(exact_lp, '_lexicographic_leaving',
                              side_effect=AssertionError('pivot past zero prefix')):
                answer = exact_lp.solve_nonnegative_kernel(matrix, cost, fast_path_pivots=0)
            self.assertEqual(answer['stats']['fallback_used'], 1)
            self.assertEqual(answer['stats']['pivots'], 0)
            self.assert_replay(matrix, cost, answer)
            prepared = exact_lp._prepare_kernel_matrix(matrix, 2)
            self.assertEqual(answer, exact_lp._solve_prepared_nonnegative_kernel(
                prepared, cost, fast_path_pivots=0))
        for cap in ('max_ellipsoid_iterations', 'max_feasibility_calls'):
            answer = exact_lp.solve_nonnegative_kernel(matrix, [1, 0],
                fast_path_pivots=0, **{cap: 0})
            self.assertEqual(answer['status'], 'INCONCLUSIVE')
            self.assertEqual(answer['stats']['fallback_used'], 1)
            self.assertEqual(answer['stats']['pivots'], 0)
            self.assert_replay(matrix, [1, 0], answer)

    def test_nested_policies_and_entries_keep_call_local_rules_and_errors(self):
        original = exact_lp._solve_prepared_kernel
        for outer, inner, outer_entry, inner_entry, error_type in product(
                ('polynomial', 'bland'), ('polynomial', 'bland'),
                ('public', 'prepared'), ('public', 'prepared'), (None, ValueError, CallerStop)):
            with self.subTest(outer=outer, inner=inner, outer_entry=outer_entry,
                              inner_entry=inner_entry, error_type=error_type):
                calls, fired = [], [False]
                error = error_type('inner cancellation') if error_type else None
                def traced(*args, **options):
                    calls.append(options.get('pivot_rule', 'bland'))
                    return original(*args, **options)
                def outer_check():
                    if fired[0] or helper_depth() != 1:
                        return
                    fired[0] = True
                    def inner_check():
                        if error is not None and helper_depth() == 2:
                            raise error
                    result = self.entry(inner_entry, [[1, -1]], [1, -2],
                        policy=inner, check=inner_check)
                    self.assert_replay([[1, -1]], [1, -2], result)
                with patch.object(exact_lp, '_solve_prepared_kernel', side_effect=traced):
                    if error is None:
                        actual = self.entry(outer_entry, [[1, 1, -1]], [1, 1, 0],
                            policy=outer, check=outer_check)
                        expected = self.entry(outer_entry, [[1, 1, -1]], [1, 1, 0], policy=outer)
                        self.assertEqual(actual, expected)
                        self.assert_replay([[1, 1, -1]], [1, 1, 0], actual)
                    else:
                        with self.assertRaises(BaseException) as caught:
                            self.entry(outer_entry, [[1, 1, -1]], [1, 1, 0],
                                policy=outer, check=outer_check)
                        self.assertIs(caught.exception, error)
                self.assertTrue(fired[0])
                expected_rules = ['dantzig_lex' if p == 'polynomial' else 'bland' for p in (outer, inner)]
                self.assertEqual(calls[:2], expected_rules)
                self.assertEqual(len(calls), 3 if error is None else 2)
                self.assertIs(exact_lp._solve_prepared_kernel, original)

    def test_callback_identity_at_all_prefix_polls_and_fallback_sites(self):
        for cost in ([1, 0], [1, -2]):
            count = [0]
            def record():
                count[0] += 1
            exact_lp.solve_nonnegative_kernel([[1, -1]], cost, check=record)
            for stop in range(1, count[0]+1):
                seen, error = [0], ValueError('prefix') if stop % 2 else CallerStop('prefix')
                def cancel():
                    seen[0] += 1
                    if seen[0] == stop:
                        raise error
                with self.assertRaises(BaseException) as caught:
                    exact_lp.solve_nonnegative_kernel([[1, -1]], cost, check=cancel)
                self.assertIs(caught.exception, error)
        sites = {}
        for cost in ([1, 0], [1, -2]):
            def record_site():
                caller = inspect.currentframe().f_back
                sites.setdefault((caller.f_code.co_filename, caller.f_code.co_name, caller.f_lineno), cost)
            exact_lp.solve_nonnegative_kernel([[1, -1]], cost,
                fast_path_pivots=0, check=record_site)
        for ordinal, (site, cost) in enumerate(sites.items()):
            error = ValueError('fallback') if ordinal % 2 else CallerStop('fallback')
            def cancel_site():
                caller = inspect.currentframe().f_back
                if (caller.f_code.co_filename, caller.f_code.co_name, caller.f_lineno) == site:
                    raise error
            with self.assertRaises(BaseException) as caught:
                exact_lp.solve_nonnegative_kernel([[1, -1]], cost,
                    fast_path_pivots=0, check=cancel_site)
            self.assertIs(caught.exception, error)

    def test_strict_controls_reject_before_dispatch(self):
        for entry in ('public', 'prepared'):
            for options in (dict(policy=True), dict(policy='dantzig_lex'),
                    dict(max_pivots=True), dict(max_pivots=-1), dict(fast_path_pivots=1.0),
                    dict(max_ellipsoid_iterations=False), dict(max_feasibility_calls=-1),
                    dict(check=None), dict(policy='bland', fast_path_pivots=0),
                    dict(policy='bland', max_feasibility_calls=0)):
                with patch.object(exact_lp, '_run_kernel_policy', side_effect=AssertionError('invalid dispatch')):
                    with self.assertRaises(ValueError):
                        self.entry(entry, [[1, -1]], [1, 0], **options)
        for rule in (True, None, 'unknown'):
            with self.assertRaises(ValueError):
                exact_lp._solve_prepared_kernel([], [], [], max_pivots=0,
                    check=lambda: None, pivot_rule=rule)

    def test_tree_and_transversal_match_tuple_rule_and_independent_replay(self):
        source = layered_torus(2)[0]
        masks = ([(0, 1), (1, 0), (1, 1), (1, 2)], [(0, 2), (1, 2)])
        for search, mask in product((tree.search_euler_tree, search_euler_transversal), masks):
            actual = search(source, mask)
            with patch.object(exact_lp, '_lexicographic_leaving', tuple_leaving):
                expected = search(source, mask)
            self.assertEqual(actual, expected)
            if actual['status'] == 'NO_POSITIVE_EULER':
                self.assertTrue(verify_euler_branch_tree(source, actual['certificate']))
            else:
                self.assertEqual(actual['status'], 'POSITIVE_EULER')
                certificate = crush_normal_ray(source, actual['coordinates'])['certificate']
                self.assertTrue(verify_normal_crushing(source, certificate))


if __name__ == '__main__':
    unittest.main()
