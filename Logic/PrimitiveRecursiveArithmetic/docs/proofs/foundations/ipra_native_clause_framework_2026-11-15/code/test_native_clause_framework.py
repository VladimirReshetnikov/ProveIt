from fractions import Fraction
import unittest

from native_clause_framework import (
    ContractNode,
    DemandNode,
    backward_demands,
    bounded_enumeration,
    bounded_least,
    bounded_monotone_closure,
    check_monotone_on_box,
    check_strict_lex_descent,
    common_good_window,
    exact_label_from_gap,
    execute_contract_graph,
    finite_descent_fuel,
    height_from_complete_list,
    list_from_height,
    relational_viability,
    stable_observation,
    tail_bound,
    verified_trace,
)


class NativeClauseFrameworkTests(unittest.TestCase):
    def test_bounded_least(self):
        self.assertEqual(bounded_least(20, lambda x: x * x >= 50), 8)
        self.assertIsNone(bounded_least(5, lambda x: x > 9))

    def test_bounded_enumeration(self):
        self.assertEqual(bounded_enumeration(12, lambda x: x % 4 == 1), (1, 5, 9))

    def test_monotone_closure(self):
        bounds = (4, 5, 3)

        def f(x):
            return (min(4, x[1]), min(5, x[0] + 1), min(3, x[1] // 2))

        self.assertTrue(check_monotone_on_box(bounds, f))
        fixed, history = bounded_monotone_closure(bounds, f)
        self.assertEqual(fixed, (4, 5, 2))
        self.assertLessEqual(len(history) - 1, sum(bounds) + 1)
        self.assertTrue(all(a <= b for a, b in zip(f(fixed), fixed, strict=True)))

    def test_backward_demands(self):
        nodes = [
            DemandNode("input", (), lambda d: {}),
            DemandNode("square", ("input",), lambda d: {"input": (d[0] + 1, d[1])}),
            DemandNode(
                "sum",
                ("input", "square"),
                lambda d: {"input": (d[0], d[1] + 2), "square": (d[0] + 2, d[1])},
            ),
        ]
        got = backward_demands(nodes, "sum", (3, 4))
        self.assertEqual(got["square"], (5, 4))
        self.assertEqual(got["input"], (6, 6))

    def test_verified_trace(self):
        result = verified_trace(1, lambda t, x: x + 2 * t + 3, lambda t, x: x == (t + 1) ** 2, 8)
        self.assertTrue(result.invariant_holds)
        self.assertEqual(result.states[-1], 81)

    def test_relational_viability(self):
        layers = [(0, 1, 2), (2, 3, 4), (4, 5, 6)]
        result = relational_viability(
            layers,
            lambda q, x, y: y in (x + 2, x + 3),
            good=lambda q, x: not (q == 1 and x == 3),
        )
        self.assertEqual(result.least_path, (0, 2, 4))
        self.assertIn(0, result.viable[0])

    def test_relational_failure(self):
        result = relational_viability([(0,), (1,), (2,)], lambda q, x, y: False)
        self.assertIsNone(result.least_path)

    def test_stable_observation(self):
        obs, diameter = stable_observation(
            [0, 1, 2],
            lambda w: Fraction(10 + w, 100),
            lambda x, y: abs(x - y),
            Fraction(1, 50),
        )
        self.assertEqual(obs, Fraction(1, 10))
        self.assertEqual(diameter, Fraction(1, 50))

    def test_tail_bound(self):
        motion = [Fraction(1, 2 ** (q + 2)) for q in range(8)]
        self.assertLess(tail_bound(motion, 3), Fraction(1, 8))

    def test_gap_recovery(self):
        labels = [Fraction(0), Fraction(1), Fraction(3)]
        idx = exact_label_from_gap(Fraction(11, 10), labels, Fraction(1, 5), Fraction(1))
        self.assertEqual(idx, 1)

    def test_height_list_equivalence(self):
        values = list_from_height(30, lambda x: x * x % 31 == 1)
        self.assertEqual(values, (1, 30))
        self.assertEqual(height_from_complete_list(values), 30)

    def test_common_window(self):
        forbidden = [{10, 11}, {12, 14, 16}, {10, 13}]
        n = common_good_window(10, forbidden)
        self.assertEqual(n, 15)

    def test_descent_fuel(self):
        self.assertEqual(finite_descent_fuel((2, 3, 1)), 24)
        self.assertTrue(check_strict_lex_descent([(2, 0), (1, 9), (1, 3), (0, 8)]))

    def test_contract_graph(self):
        nodes = [
            ContractNode("a", (), lambda _e: 7, lambda _e, x: x == 7),
            ContractNode("b", ("a",), lambda e: e["a"] * e["a"], lambda e, x: x == e["a"] ** 2),
            ContractNode(
                "c",
                ("a", "b"),
                lambda e: e["a"] + e["b"],
                lambda e, x: x - e["b"] == e["a"],
            ),
        ]
        self.assertEqual(execute_contract_graph(nodes)["c"], 56)


if __name__ == "__main__":
    unittest.main(verbosity=2)
