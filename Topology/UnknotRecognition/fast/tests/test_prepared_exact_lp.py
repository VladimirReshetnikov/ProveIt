"""Reusable LP parsing/row selection with fresh per-objective solver state."""
from copy import deepcopy
from fractions import Fraction as Q
import inspect
from math import gcd
import unittest
from unittest.mock import patch

from fastunknot import exact_lp
from fastunknot import normal_euler_tree as tree_module
from fastunknot.integer_codec import encoded_integer
from fastunknot.normal_crushing import crush_normal_ray
from fastunknot.normal_crushing_verify import verify_normal_crushing
from fastunknot.normal_euler_transversal import search_euler_transversal
from fastunknot.normal_euler_tree_verify import verify_euler_branch_tree
from normal_orbit_research.fixtures import layered_torus
from tests.test_polynomial_exact_lp import normalized_vertices


def rational(value):
    if type(value) is Q:
        return value
    if type(value) in (list, tuple):
        return Q(*(encoded_integer(x) for x in value))
    return Q(encoded_integer(value))


class CallerStop(BaseException):
    pass


class PreparedExactLPTests(unittest.TestCase):
    def assert_replay(self, matrix, objective, answer):
        matrix = [[rational(a) for a in row] for row in matrix]
        cost = [rational(a) for a in objective]
        self.assertIs(type(answer['equation_rows']), list)
        if answer['status'] == 'INCONCLUSIVE':
            self.assertTrue(set(answer).isdisjoint({'x', 'y', 'primitive_x', 'basis'}))
            return
        vertices = normalized_vertices(matrix, len(cost))
        positive = any(sum(a*x for a, x in zip(cost, point)) > 0 for point in vertices)
        self.assertEqual(answer['status'], 'POSITIVE' if positive else 'NONPOSITIVE')
        if positive:
            point = tuple(rational(x) for x in answer['x'])
            self.assertIn(point, vertices)  # Independent Leibniz/Cramer extremality.
            self.assertEqual(sum(point), 1)
            self.assertTrue(all(sum(a*x for a, x in zip(row, point)) == 0 for row in matrix))
            self.assertEqual(sum(a*x for a, x in zip(cost, point)), rational(answer['objective']))
            ray = answer['primitive_x']
            self.assertTrue(all(type(a) is int and a >= 0 for a in ray))
            self.assertEqual(gcd(*ray), 1)
            self.assertEqual(tuple(Q(a, sum(ray)) for a in ray), point)
        else:
            dual = [rational(a) for a in answer['y']]
            self.assertEqual(len(dual), len(matrix))
            for j, c in enumerate(cost):
                self.assertGreaterEqual(sum(row[j]*a for row, a in zip(matrix, dual)), c)

    def compare(self, prepared, matrix, objective, **options):
        expected = exact_lp.solve_nonnegative_kernel(
            matrix, objective, reduce_rows=prepared.reduce_rows, **options)
        actual = exact_lp._solve_prepared_nonnegative_kernel(prepared, objective, **options)
        self.assertEqual(actual, expected)
        self.assert_replay(matrix, objective, actual)
        return actual

    def test_successive_objectives_match_complete_fresh_results(self):
        cases = [([], [[], []]), ([[], []], [[], []]),
                 ([], [[1, -1], [-1, 0], [0, 0]]),
                 ([[0, 0], [Q(1, 2), -1], [1, -2]],
                  [[1, 0], [1, -3], [0, 0]]),
                 ([[[1, 2], '-0x1'], [[1, 1], -2]],
                  [[[1, 3], 0], [1, -3]])]
        for matrix, objectives in cases:
            for reduce_rows in (False, True):
                prepared = exact_lp._prepare_kernel_matrix(
                    matrix, len(objectives[0]), reduce_rows=reduce_rows)
                for policy in ('bland', 'polynomial'):
                    for objective in objectives + objectives[:1]:
                        with self.subTest(matrix=matrix, objective=objective,
                                          reduce_rows=reduce_rows, policy=policy):
                            self.compare(prepared, matrix, objective, policy=policy)

    def test_forced_fallback_positive_dual_and_large_rational_rows(self):
        for matrix, objectives in (([[1, -1], [2, -2], [0, 0]], [[1, 0], [1, -2]]),
                ([[Q(1, 1 << 256), Q(-2, 1 << 256)], [1, -2]], [[1, -3]])):
            for reduce_rows in (False, True):
                prepared = exact_lp._prepare_kernel_matrix(matrix, 2, reduce_rows=reduce_rows)
                for objective in objectives:
                    with self.subTest(objective=objective, reduce_rows=reduce_rows):
                        answer = self.compare(prepared, matrix, objective, fast_path_pivots=0)
                        self.assertEqual(answer['stats']['fallback_used'], 1)
                        self.assertEqual(answer['stats']['pivots'], 0)

    def test_huge_encoded_inputs_keep_exact_source_rows_and_ray(self):
        huge = 1 << 20000
        matrix, objective = [[1, '-'+hex(huge)]], [1, 0]
        prepared = exact_lp._prepare_kernel_matrix(matrix, 2)
        answer = self.compare(prepared, matrix, objective)
        self.assertEqual(answer['primitive_x'], [huge, 1])
        self.assertEqual(prepared.source, ((Q(1), Q(-huge)),))

    def test_context_and_returned_mutable_fields_are_isolated(self):
        matrix, objective = [[1, -1], [2, -2]], [1, 0]
        original = deepcopy(matrix)
        prepared = exact_lp._prepare_kernel_matrix(matrix, 2)
        before = deepcopy(prepared)
        answer = self.compare(prepared, original, objective)
        self.assertIs(type(prepared.source), tuple)
        self.assertTrue(all(type(row) is tuple for row in prepared.source))
        self.assertIs(type(prepared.selected), tuple)
        with self.assertRaises((AttributeError, TypeError)):
            prepared.width = 7
        with self.assertRaises(TypeError):
            prepared.source[0][0] = Q(9)
        with self.assertRaises(TypeError):
            prepared.selected[0] = 9
        matrix[0][0] = 400
        matrix.append([7])
        objective[0] = -500
        answer['equation_rows'].append(99)
        answer['basis'].clear()
        answer['x'][0][0] += 42
        answer['primitive_x'][0] += 42
        answer['stats']['pivots'] = 10000
        self.compare(prepared, original, [1, 0])
        negative = self.compare(prepared, original, [1, -2])
        negative['y'][0][0] += 100
        negative['equation_rows'].clear()
        self.compare(prepared, original, [1, -2])
        self.assertEqual(prepared, before)

    def test_each_call_has_fresh_allowances_and_zero_pivot_conclusions(self):
        matrix, objective = [[1, -1]], [1, 0]
        prepared = exact_lp._prepare_kernel_matrix(matrix, 2)
        full = self.compare(prepared, matrix, objective)
        self.compare(prepared, matrix, objective, max_pivots=full['stats']['pivots'])
        self.compare(prepared, matrix, objective, max_pivots=full['stats']['pivots']-1)
        for options in (dict(max_pivots=0), dict(policy='bland', max_pivots=0),
                        dict(fast_path_pivots=0, max_pivots=0),
                        dict(fast_path_pivots=0, max_ellipsoid_iterations=0),
                        dict(fast_path_pivots=0, max_ellipsoid_iterations=1),
                        dict(fast_path_pivots=0, max_feasibility_calls=0),
                        dict(fast_path_pivots=0, max_feasibility_calls=1)):
            with self.subTest(options=options):
                answer = self.compare(prepared, matrix, objective, **options)
                self.assertEqual(answer['status'], 'INCONCLUSIVE')
                if options.get('max_pivots') == 0:
                    self.assertEqual(answer['stats'].get('fallback_used', 0), 0)
        zero = self.compare(prepared, matrix, [-1, 0], max_pivots=0)
        self.assertEqual(zero['status'], 'NONPOSITIVE')
        self.assertEqual(zero['stats']['pivots'], 0)
        self.assertEqual(self.compare(prepared, matrix, objective), full)

    def test_preparation_objective_and_control_validation_is_strict(self):
        for matrix, width in (({}, 1), ([True], 1), ([[1]], 2),
                ([[True]], 1), ([[1.0]], 1), ([[[1, 0]]], 1),
                ([[[1, False]]], 1), ([], True), ([], -1), ([], 1.0)):
            with self.subTest(matrix=matrix, width=width), self.assertRaises(ValueError):
                exact_lp._prepare_kernel_matrix(matrix, width)
        for reduce in (None, 0, 1, 'true'):
            with self.assertRaises(ValueError):
                exact_lp._prepare_kernel_matrix([], 0, reduce_rows=reduce)
        with self.assertRaises(ValueError):
            exact_lp._prepare_kernel_matrix([], 0, check=None)
        prepared = exact_lp._prepare_kernel_matrix([[1, -1]], 2)
        for objective in ({}, [1], [1, 0, 0], [True, 0], [1.0, 0],
                          [[[1, 0]], 0], [[1, -1], 0], [[1, True], 0]):
            with self.subTest(objective=objective), self.assertRaises(ValueError):
                exact_lp._solve_prepared_nonnegative_kernel(prepared, objective)
        for bad in (None, {}, [], prepared.source):
            with self.assertRaises(ValueError):
                exact_lp._solve_prepared_nonnegative_kernel(bad, [1, 0])
        for options in (dict(policy=True), dict(policy='unknown'), dict(max_pivots=True),
                        dict(max_pivots=-1), dict(fast_path_pivots=0.5),
                        dict(max_ellipsoid_iterations=False), dict(max_feasibility_calls=-1),
                        dict(check=None), dict(policy='bland', fast_path_pivots=0),
                        dict(policy='bland', max_feasibility_calls=0)):
            with self.subTest(options=options), self.assertRaises(ValueError):
                exact_lp._solve_prepared_nonnegative_kernel(prepared, [1, 0], **options)
        self.compare(prepared, [[1, -1]], [1, 0])

    def test_callback_identity_at_every_preparation_and_reused_fast_poll(self):
        matrix = [[0, 0], [1, -1], [2, -2]]
        prepared = exact_lp._prepare_kernel_matrix(matrix, 2)
        actions = [lambda check: exact_lp._prepare_kernel_matrix(matrix, 2, check=check),
                   lambda check: exact_lp._solve_prepared_nonnegative_kernel(
                       prepared, [1, 0], check=check),
                   lambda check: exact_lp._solve_prepared_nonnegative_kernel(
                       prepared, [1, 0], fast_path_pivots=0,
                       max_ellipsoid_iterations=0, check=check)]
        errors = (ValueError, TypeError, ArithmeticError, KeyboardInterrupt, SystemExit, CallerStop)
        for action in actions:
            count = [0]
            def record():
                count[0] += 1
            action(record)
            self.assertGreater(count[0], 0)
            for stop in range(1, count[0]+1):
                current, error = [0], errors[stop % len(errors)]('caller cancellation')
                def cancel():
                    current[0] += 1
                    if current[0] == stop:
                        raise error
                try:
                    action(cancel)
                except BaseException as caught:
                    self.assertIs(caught, error)
                else:
                    self.fail('callback poll disappeared')

    def test_callback_identity_at_every_complete_fallback_poll_site(self):
        # Repeated ellipsoid cuts use the same sites; visiting every distinct
        # site covers complete positive/dual recovery without quadratic runs.
        prepared = exact_lp._prepare_kernel_matrix([[1, -1]], 2)
        sites = {}
        for objective in ([1, 0], [1, -2]):
            def record():
                frame = inspect.currentframe().f_back
                sites.setdefault((frame.f_code.co_filename, frame.f_code.co_name, frame.f_lineno),
                                 objective)
            exact_lp._solve_prepared_nonnegative_kernel(
                prepared, objective, fast_path_pivots=0, check=record)
        self.assertTrue(any(name == '_replay_fallback' for _, name, _ in sites))
        self.assertTrue(any(name == 'find_point' for _, name, _ in sites))
        for index, (site, objective) in enumerate(sites.items()):
            error = (ValueError, KeyboardInterrupt, CallerStop)[index % 3]('caller cancellation')
            def cancel():
                frame = inspect.currentframe().f_back
                if (frame.f_code.co_filename, frame.f_code.co_name, frame.f_lineno) == site:
                    raise error
            try:
                exact_lp._solve_prepared_nonnegative_kernel(
                    prepared, objective, fast_path_pivots=0, check=cancel)
            except BaseException as caught:
                self.assertIs(caught, error)
            else:
                self.fail('fallback callback site disappeared: '+str(site))


class PreparedEulerOracleTests(unittest.TestCase):
    def setUp(self):
        self.source = layered_torus(2)[0]
        self.negative = [(0, 1), (1, 0), (1, 1), (1, 2)]

    def assert_result_replay(self, result):
        if result['status'] == 'NO_POSITIVE_EULER':
            self.assertTrue(verify_euler_branch_tree(self.source, result['certificate']))
        elif result['status'] == 'POSITIVE_EULER':
            # Full original-support/extremality and quotient replay, separate
            # from the Euler producer and its prepared LP bookkeeping.
            packet = crush_normal_ray(self.source, result['coordinates'])['certificate']
            self.assertTrue(verify_normal_crushing(self.source, packet))
        else:
            self.assertEqual(result['status'], 'INCONCLUSIVE')
            self.assertNotIn('certificate', result)

    @staticmethod
    def fresh_solve(prepared, objective, **options):
        return exact_lp.solve_nonnegative_kernel(prepared.source, objective,
                                                reduce_rows=prepared.reduce_rows, **options)

    def test_full_tree_and_transversal_outputs_equal_fresh_objective_solves(self):
        for search in (tree_module.search_euler_tree, search_euler_transversal):
            models = ('source', 'restricted') if search is tree_module.search_euler_tree else ('source',)
            for model in models:
                model_options = dict(model=model) if search is tree_module.search_euler_tree else {}
                for mask, options in ((self.negative, {}), ([(0, 2), (1, 2)], {}),
                        (self.negative, dict(strategy='anchors', max_pivots=3)),
                        (self.negative, dict(lp_fast_path_pivots=0,
                                             max_ellipsoid_iterations=0))):
                    with self.subTest(search=search.__name__, model=model, options=options):
                        actual = search(self.source, mask, **model_options, **options)
                        with patch.object(tree_module, '_solve_prepared_nonnegative_kernel',
                                          side_effect=self.fresh_solve):
                            expected = search(self.source, mask, **model_options, **options)
                        self.assertEqual(actual, expected)
                        self.assert_result_replay(actual)

    def test_row_selection_once_per_attempt_never_across_masks(self):
        prepare = tree_module._prepare_kernel_matrix
        solve = tree_module._solve_prepared_nonnegative_kernel
        attempt = tree_module._EulerMaskOracle.attempt
        for search in (tree_module.search_euler_tree, search_euler_transversal):
            models = ('source', 'restricted') if search is tree_module.search_euler_tree else ('source',)
            for model in models:
                model_options = dict(model=model) if search is tree_module.search_euler_tree else {}
                attempts, current = [], []
                def attempted(oracle, mask):
                    record = dict(mask=tuple(mask), contexts=[], solves=[])
                    attempts.append(record)
                    current.append(record)
                    try:
                        return attempt(oracle, mask)
                    finally:
                        current.pop()
                def prepared(matrix, width, **options):
                    with patch.object(exact_lp, '_independent_rows',
                                      wraps=exact_lp._independent_rows) as rows:
                        context = prepare(matrix, width, **options)
                    self.assertEqual(rows.call_count, 1)
                    current[-1]['contexts'].append(context)
                    return context
                def solved(context, objective, **options):
                    current[-1]['solves'].append(context)
                    return solve(context, objective, **options)
                with patch.object(tree_module._EulerMaskOracle, 'attempt', attempted), \
                     patch.object(tree_module, '_prepare_kernel_matrix', side_effect=prepared), \
                     patch.object(tree_module, '_solve_prepared_nonnegative_kernel', side_effect=solved):
                    result = search(self.source, self.negative, **model_options)
                self.assert_result_replay(result)
                self.assertTrue(any(len(record['solves']) > 1 for record in attempts))
                self.assertGreater(len({record['mask'] for record in attempts}), 1)
                contexts = []
                for record in attempts:
                    self.assertEqual(len(record['contexts']), int(bool(record['solves'])))
                    if record['solves']:
                        context = record['contexts'][0]
                        self.assertTrue(all(item is context for item in record['solves']))
                        self.assertEqual(context.width, len(record['mask']))
                        contexts.append(context)
                self.assertEqual(len({id(context) for context in contexts}), len(contexts))
                self.assertEqual(sum(len(record['solves']) for record in attempts),
                                 result['stats']['lp_calls'])

    def test_all_cached_or_denied_attempts_do_not_prepare_lp(self):
        for search in (tree_module.search_euler_tree, search_euler_transversal):
            for mask, options, expected in (
                    ([], dict(max_pivots=0, max_anchors=0), 'NO_POSITIVE_EULER'),
                    ([], dict(strategy='anchors'), 'NO_POSITIVE_EULER'),
                    (self.negative, dict(strategy='anchors', max_anchors=0), 'INCONCLUSIVE'),
                    (self.negative, dict(max_nodes=0), 'INCONCLUSIVE')):
                with patch.object(tree_module, '_prepare_kernel_matrix',
                                  side_effect=AssertionError('unnecessary LP preparation')):
                    result = search(self.source, mask, **options)
                self.assertEqual(result['status'], expected)
                self.assertEqual(result['stats']['lp_calls'], 0)
                self.assert_result_replay(result)


if __name__ == '__main__':
    unittest.main()
