from __future__ import annotations

import json
import unittest
from fractions import Fraction
from pathlib import Path

from kffu import (
    ContractError,
    ContractNode,
    backward_viability,
    compile_contract_dag,
    cubic_bisection_certificate,
    enumerate_paths,
    fraction_from_record,
    lexicographic_viable_path,
    observation_diameter,
    verify_cubic_bisection_certificate,
)


class ContractDAGTests(unittest.TestCase):
    def test_checked_dag(self) -> None:
        nodes = [
            ContractNode(
                "double",
                ("x",),
                lambda env: 2 * env["x"],
                lambda env, out: out == env["x"] + env["x"],
            ),
            ContractNode(
                "square",
                ("double",),
                lambda env: env["double"] ** 2,
                lambda env, out: out == env["double"] * env["double"],
            ),
            ContractNode(
                "summary",
                ("x", "square"),
                lambda env: env["square"] + env["x"],
                lambda env, out: out - env["square"] == env["x"],
            ),
        ]
        env, trace = compile_contract_dag(nodes, {"x": 7})
        self.assertEqual(env["summary"], 203)
        self.assertEqual([entry.name for entry in trace], ["double", "square", "summary"])

    def test_forward_reference_rejected(self) -> None:
        node = ContractNode("bad", ("later",), lambda env: 0, lambda env, out: True)
        with self.assertRaises(ContractError):
            compile_contract_dag([node])

    def test_failed_local_checker_rejected(self) -> None:
        node = ContractNode("bad", (), lambda env: 3, lambda env, out: out == 4)
        with self.assertRaises(ContractError):
            compile_contract_dag([node])


class ViabilityTests(unittest.TestCase):
    def setUp(self) -> None:
        self.layers = [(0, 1, 2), (1, 2, 3), (3, 4), (4, 5)]
        self.compat = lambda i, x, y: abs(int(y) - int(x)) <= 1

    def test_backward_viability_and_path(self) -> None:
        viable = backward_viability(self.layers, self.compat)
        self.assertEqual(viable[0], (1, 2))
        path = lexicographic_viable_path(self.layers, self.compat)
        self.assertEqual(path, (1, 2, 3, 4))
        self.assertIn(path, enumerate_paths(self.layers, self.compat))

    def test_stable_observable(self) -> None:
        paths = enumerate_paths(self.layers, self.compat)
        # The normalized endpoint is stable to diameter 1 despite nonunique paths.
        diameter = observation_diameter(paths, lambda p: Fraction(int(p[-1]), 5))
        self.assertEqual(diameter, Fraction(1, 5))

    def test_no_path(self) -> None:
        layers = [(0,), (5,)]
        with self.assertRaises(ContractError):
            lexicographic_viable_path(layers, lambda i, x, y: abs(y - x) <= 1)


class CubicTests(unittest.TestCase):
    def test_exact_certificate(self) -> None:
        for x in [Fraction(0), Fraction(3, 2), Fraction(-17, 5), Fraction(101, 7)]:
            for precision in [0, 1, 5, 12]:
                cert = cubic_bisection_certificate(x, precision)
                self.assertTrue(verify_cubic_bisection_certificate(cert))
                lo = fraction_from_record(cert["final_lo"])
                hi = fraction_from_record(cert["final_hi"])
                self.assertLessEqual(hi - lo, Fraction(1, 2**precision))

    def test_tampering_detected(self) -> None:
        cert = cubic_bisection_certificate(Fraction(7, 3), 6)
        cert = json.loads(json.dumps(cert))
        cert["trace"][0]["branch"] = "left" if cert["trace"][0]["branch"] == "right" else "right"
        with self.assertRaises(ContractError):
            verify_cubic_bisection_certificate(cert)

    def test_checked_example_file(self) -> None:
        path = Path(__file__).resolve().parents[1] / "examples" / "cubic_certificate.json"
        if path.exists():
            with path.open(encoding="utf-8") as handle:
                self.assertTrue(verify_cubic_bisection_certificate(json.load(handle)))


if __name__ == "__main__":
    unittest.main(verbosity=2)
