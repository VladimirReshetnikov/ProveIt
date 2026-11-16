from __future__ import annotations

import json
import unittest
from fractions import Fraction
from pathlib import Path

from finitary_kernel import (
    ContractDAG,
    FiniteRelationTower,
    GuardResult,
    InterfaceNode,
    RationalBall,
    TraceSystem,
    bounded_all,
    bounded_any,
    bounded_least,
    cubic,
    cubic_inverse_ball,
    cubic_inverse_certificate,
    finite_net_minimum,
    guarded_reciprocal,
    height_bound_from_complete_integer_list,
    integer_points_from_height_bound,
    run_trace,
    three_way_guard,
    trace_reflection_instance,
    verify_cubic_inverse_certificate,
    verify_trace,
)


class BoundedTests(unittest.TestCase):
    def test_bounded_booleanization(self) -> None:
        self.assertTrue(bounded_all(8, lambda i: i < 8))
        self.assertTrue(bounded_any(8, lambda i: i == 6))
        self.assertEqual(bounded_least(20, lambda i: i * i >= 30), 6)
        with self.assertRaises(LookupError):
            bounded_least(4, lambda _i: False)


class TraceTests(unittest.TestCase):
    @staticmethod
    def triangular_system() -> TraceSystem:
        return TraceSystem(
            good=lambda u: u >= 0,
            init=lambda _u: 0,
            bound=lambda u: u,
            step=lambda i, state, _u: state + i + 1,
            invariant=lambda i, state, _u: 2 * state == i * (i + 1),
            accept=lambda state, u: 2 * state == u * (u + 1),
        )

    def test_trace_certificate(self) -> None:
        system = self.triangular_system()
        states = run_trace(system, 25)
        self.assertTrue(verify_trace(system, 25, states))
        self.assertTrue(trace_reflection_instance(system, 25))
        damaged = list(states)
        damaged[8] += 1
        self.assertFalse(verify_trace(system, 25, damaged))


class ContractDAGTests(unittest.TestCase):
    def test_reverse_demands_and_execution(self) -> None:
        source = InterfaceNode(
            "source",
            (),
            lambda _q: (),
            lambda _args, q: (q, Fraction(1, 3)),
            lambda _args, q, out: out[0] == q,
        )
        square = InterfaceNode(
            "square",
            ("source",),
            lambda q: (q + 2,),
            lambda args, q: (q, args[0][1] ** 2),
            lambda args, q, out: out == (q, args[0][1] ** 2),
        )
        shift = InterfaceNode(
            "shift",
            ("square",),
            lambda q: (q + 1,),
            lambda args, q: (q, args[0][1] + 1),
            lambda args, q, out: out == (q, args[0][1] + 1),
        )
        dag = ContractDAG([source, square, shift])
        result, values, demands = dag.execute("shift", 7)
        self.assertEqual(demands, {"source": 10, "square": 8, "shift": 7})
        self.assertEqual(result, (7, Fraction(10, 9)))
        self.assertEqual(values["source"][0], 10)


class RelationalTests(unittest.TestCase):
    def test_backward_viability(self) -> None:
        tower = FiniteRelationTower(
            levels=((0, 3), (1, 4), (2, 7), (3,)),
            edge=lambda _i, a, b: abs(a - b) <= 1,
        )
        viability = tower.viability()
        self.assertEqual(viability[0], frozenset({0}))
        self.assertEqual(tower.least_path(), (0, 1, 2, 3))

    def test_path_independent_observation(self) -> None:
        tower = FiniteRelationTower(
            levels=((0, 1), (0, 1), (0, 1)),
            edge=lambda _i, _a, _b: True,
        )
        observations = tower.terminal_observations(lambda x: x % 1)
        self.assertEqual(set(observations), {0})


class GuardTests(unittest.TestCase):
    def test_three_way_guard(self) -> None:
        self.assertEqual(
            three_way_guard(Fraction(-5, 4), Fraction(1, 4)),
            GuardResult.NEGATIVE,
        )
        self.assertEqual(
            three_way_guard(Fraction(5, 4), Fraction(1, 4)),
            GuardResult.POSITIVE,
        )
        self.assertEqual(
            three_way_guard(Fraction(1, 10), Fraction(1, 5)),
            GuardResult.UNRESOLVED,
        )

    def test_guarded_reciprocal(self) -> None:
        ball = RationalBall(Fraction(3, 1), Fraction(1, 4))
        reciprocal = guarded_reciprocal(ball)
        for x in (Fraction(11, 4), Fraction(3), Fraction(13, 4)):
            self.assertTrue(reciprocal.contains(1 / x))
        with self.assertRaises(ValueError):
            guarded_reciprocal(RationalBall(Fraction(1, 10), Fraction(1, 5)))


class CubicTests(unittest.TestCase):
    def test_cubic_inverse_regular_name(self) -> None:
        x = Fraction(2)
        coarse = cubic_inverse_ball(x, 8)
        fine = cubic_inverse_ball(x, 18)
        self.assertTrue(coarse.overlaps(fine))
        self.assertLessEqual(coarse.radius, Fraction(1, 2 ** 10))
        self.assertLessEqual(fine.radius, Fraction(1, 2 ** 20))
        self.assertLessEqual(abs(cubic(coarse.center) - x), Fraction(1, 100))

    def test_cubic_certificate(self) -> None:
        cert = cubic_inverse_certificate(Fraction(2), 12)
        self.assertTrue(verify_cubic_inverse_certificate(cert))
        damaged = json.loads(json.dumps(cert))
        damaged["trace"][3]["hi"] = "999"
        self.assertFalse(verify_cubic_inverse_certificate(damaged))


class HeightAndNetTests(unittest.TestCase):
    def test_height_list_equivalence_instance(self) -> None:
        pred = lambda z: z * z <= 16 and z % 2 == 0
        points = integer_points_from_height_bound(4, pred)
        self.assertEqual(points, (-4, -2, 0, 2, 4))
        self.assertEqual(height_bound_from_complete_integer_list(points, pred), 4)

    def test_finite_net_minimum(self) -> None:
        points = [Fraction(-2), Fraction(-1), Fraction(0), Fraction(1)]
        point, value = finite_net_minimum(points, lambda x: (x - Fraction(1, 3)) ** 2)
        self.assertEqual(point, Fraction(0))
        self.assertEqual(value, Fraction(1, 9))


if __name__ == "__main__":
    unittest.main(verbosity=2)
