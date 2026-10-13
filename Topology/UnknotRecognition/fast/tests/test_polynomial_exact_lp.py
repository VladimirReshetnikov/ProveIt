"""Exact polynomial-policy controls with an independent small-cone oracle."""
from copy import deepcopy
from fractions import Fraction as Q
from itertools import combinations, permutations
import inspect
import json
import unittest
from unittest.mock import patch

from fastunknot import exact_lp
from fastunknot import bounded_lp
from fastunknot.integer_codec import json_safe


def determinant(matrix):
    n, total = len(matrix), Q(0)
    for order in permutations(range(n)):
        value = Q((-1)**sum(order[i] > order[j] for i in range(n) for j in range(i+1,n)))
        for i in range(n):
            value *= matrix[i][order[i]]
        total += value
    return total


def normalized_vertices(matrix, n):
    """Leibniz/Cramer support oracle, independent of all solver elimination."""
    found = set()
    for k in range(1,n+1):
        for support in combinations(range(n), k):
            equations = [([Q(row[j]) for j in support], Q(0)) for row in matrix]
            equations.append(([Q(1)]*k, Q(1)))
            for active in combinations(equations,k):
                square, rhs = [row for row,_ in active], [b for _,b in active]
                divisor = determinant(square)
                if not divisor:
                    continue
                values = tuple(determinant([row[:j]+[b]+row[j+1:]
                              for row,b in zip(square,rhs)])/divisor for j in range(k))
                if any(x <= 0 for x in values):
                    continue
                if any(sum(a*x for a,x in zip(row,values)) != b for row,b in equations):
                    continue
                full = [Q(0)]*n
                for j,x in zip(support,values):
                    full[j] = x
                found.add(tuple(full))
    return found


class PolynomialExactLPTests(unittest.TestCase):
    def assert_oracle(self, matrix, objective, answer):
        points = normalized_vertices(matrix, len(objective))
        positive = any(sum(a*x for a,x in zip(objective,point)) > 0 for point in points)
        self.assertEqual(answer['status'], 'POSITIVE' if positive else 'NONPOSITIVE')
        if positive:
            point = tuple(Q(*x) for x in answer['x'])
            self.assertIn(point, points)
            self.assertGreater(sum(a*x for a,x in zip(objective,point)), 0)
        else:
            dual = tuple(Q(*y) for y in answer['y'])
            self.assertEqual(len(dual),len(matrix))
            for j,c in enumerate(objective):
                self.assertGreaterEqual(sum(row[j]*y for row,y in zip(matrix,dual)), c)
        json.loads(json.dumps(json_safe(answer)))

    def test_forced_fallback_matches_independent_vertices_and_original_duals(self):
        cases = [([],[]), ([[],[]],[]), ([],[1,1,1]), ([[1]],[1]),
                 ([[1,-1]],[1,0]), ([[1,1]],[1,1]), ([[1,-1]],[1,-2]),
                 ([[Q(1,2),Q(-1,3)],[3,-2],[0,0]],[1,0]),
                 ([[Q(1,2),Q(-1,3)],[3,-2],[0,0]],[Q(1,5),Q(-1,2)]),
                 ([[1,1],[1,-1]],[1,2]), ([[1,-1,0]],[1,0,-1]),
                 ([[1,-1,0]],[1,-2,-1]), ([[1,1,-1]],[1,1,0])]
        for matrix,objective in cases:
            before = deepcopy((matrix,objective))
            for reduce in (True,False):
                with self.subTest(matrix=matrix,objective=objective,reduce=reduce):
                    answer = exact_lp.solve_nonnegative_kernel(
                        matrix,objective,reduce_rows=reduce,fast_path_pivots=0)
                    self.assert_oracle(matrix,objective,answer)
                    legacy = exact_lp.solve_nonnegative_kernel(
                        matrix,objective,reduce_rows=reduce,policy='bland')
                    self.assertEqual(answer['status'],legacy['status'])
            self.assertEqual((matrix,objective),before)

    def test_positive_recovery_descends_a_valid_nonextreme_point(self):
        # This tests continuation from a valid bounded-slice point, not LP
        # discovery: sum(x)=c*x=1 and all coordinates are strictly positive.
        with patch.object(bounded_lp,'find_point',return_value=dict(
                status='FEASIBLE',point=[Q(1,3)]*3)):
            answer = exact_lp.solve_nonnegative_kernel([], [1,1,1],fast_path_pivots=0)
        self.assert_oracle([], [1,1,1], answer)
        self.assertEqual(answer['stats']['support_descent_steps'],2)
        self.assertEqual(sum(bool(x) for x in answer['primitive_x']),1)

    def test_caps_never_emit_partial_certificates_or_charge_cuts_as_pivots(self):
        solve = exact_lp.solve_nonnegative_kernel
        for cap in (0,1,3):
            result = solve([[1,-1]],[1,0],fast_path_pivots=0,max_ellipsoid_iterations=cap)
            self.assertEqual(result['status'],'INCONCLUSIVE')
            self.assertEqual(result['stats']['pivots'],0)
            self.assertEqual(result['stats']['ellipsoid_iterations'],cap)
            self.assertTrue(set(result).isdisjoint({'x','y','basis','primitive_x'}))
        for cap in (0,1,2):
            result = solve([[1,-1]],[1,0],fast_path_pivots=0,max_feasibility_calls=cap)
            self.assertEqual(result['status'],'INCONCLUSIVE')
            self.assertEqual(result['stats']['feasibility_calls'],cap)
        result = solve([[1,-1]],[1,0],max_pivots=0)
        self.assertEqual(result['status'],'INCONCLUSIVE')
        self.assertEqual(result['stats']['fallback_used'],0)
        result = solve([[1,-1]],[1,0],fast_path_pivots=10**9)
        self.assertEqual(result['stats']['fast_path_pivot_limit'],16)

    def test_fast_path_prepares_once_and_uses_existing_basis_validation(self):
        with patch.object(exact_lp,'_independent_rows',wraps=exact_lp._independent_rows) as basis:
            with patch.object(exact_lp,'_replay_fallback',side_effect=AssertionError('extra replay')):
                answer = exact_lp.solve_nonnegative_kernel([[1,-1],[2,-2]],[1,0])
        self.assertEqual(answer['status'],'POSITIVE')
        self.assertEqual(basis.call_count,1)
        self.assertEqual(answer['stats']['fallback_used'],0)

    def test_large_exact_row_scales_map_back_to_original_dual(self):
        scale = 1 << 2048
        matrix = [[Q(1,scale),Q(-2,scale)],[1,-2]]
        answer = exact_lp.solve_nonnegative_kernel(matrix,[1,-3],fast_path_pivots=0)
        self.assert_oracle(matrix,[1,-3],answer)
        self.assertGreaterEqual(Q(*answer['y'][0]),scale)
        self.assertEqual(answer['y'][1],[0,1])

    def test_new_options_are_strict(self):
        for options in (dict(policy=True),dict(policy='float'),dict(fast_path_pivots=-1),
                        dict(max_feasibility_calls=1.0),dict(max_ellipsoid_iterations=False),
                        dict(check=None),dict(policy='bland',fast_path_pivots=0)):
            with self.subTest(options=options),self.assertRaises(ValueError):
                exact_lp.solve_nonnegative_kernel([[1,-1]],[1,0],**options)

    def test_callback_identity_at_every_visited_positive_and_dual_poll_site(self):
        sites, objective = {}, None
        def record():
            caller = inspect.currentframe().f_back
            sites.setdefault((caller.f_code.co_filename,caller.f_code.co_name,caller.f_lineno),objective)
        for objective in ([1,0],[1,-2]):
            exact_lp.solve_nonnegative_kernel([[1,-1]],objective,fast_path_pivots=0,check=record)
        for index,(site,objective) in enumerate(sites.items()):
            error = (ValueError('stop') if index%3 == 0 else
                     TypeError('stop') if index%3 == 1 else KeyboardInterrupt('stop'))
            def cancel():
                caller = inspect.currentframe().f_back
                if (caller.f_code.co_filename,caller.f_code.co_name,caller.f_lineno) == site:
                    raise error
            try:
                exact_lp.solve_nonnegative_kernel([[1,-1]],objective,fast_path_pivots=0,check=cancel)
            except BaseException as caught:
                self.assertIs(caught,error)
            else:
                self.fail('callback site not visited: '+str(site))


if __name__ == '__main__':
    unittest.main()
