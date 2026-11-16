#!/usr/bin/env python3
from __future__ import annotations

import copy
import json
import unittest
from fractions import Fraction
from pathlib import Path

from cbip_kernel import (
    Atom,
    EvidenceMachine,
    Exists,
    Forall,
    TraceSystem,
    all_below,
    any_below,
    binary_metastable_window,
    canonical_certificate,
    check_certificate,
    dyadic_grid_argmin_residual,
    enumerate_integer_pairs,
    first_success,
    formula_value,
    propagate_error,
    window_is_constant,
)


class BooleanFoldTests(unittest.TestCase):
    def test_empty_domains_and_sentinel(self) -> None:
        self.assertTrue(all_below(0, lambda _: False))
        self.assertFalse(any_below(0, lambda _: True))
        self.assertEqual(first_success(0, lambda _: True), 0)
        self.assertEqual(first_success(5, lambda i: i == 3), 3)
        self.assertEqual(first_success(5, lambda _: False), 5)


class StrategyCertificateTests(unittest.TestCase):
    @staticmethod
    def true_contract() -> Forall:
        # env layouts:
        # initial: (Q,)
        # after forall: (q,Q)
        # after exists: (z,q,Q)
        # after forall e: (e,z,q,Q)
        return Forall(
            lambda env: env[0],
            Exists(
                lambda env: 2 * env[1] + 1,
                Forall(
                    lambda env: env[1] + 1,
                    Atom(lambda env: env[1] + env[0] >= env[2], "z+e>=q"),
                    "tests",
                ),
                "witness",
            ),
            "queries",
        )

    @staticmethod
    def false_contract() -> Forall:
        # For every q<Q, ask for z<q+1 with z>=q+1: impossible already at q=0.
        return Forall(
            lambda env: env[0],
            Exists(
                lambda env: env[0] + 1,
                Atom(lambda env: env[0] >= env[1] + 1, "z>=q+1"),
                "bad_witness",
            ),
            "queries",
        )

    def test_success_strategy(self) -> None:
        formula = self.true_contract()
        env = (5,)
        cert = canonical_certificate(formula, env)
        self.assertTrue(formula_value(formula, env))
        self.assertTrue(cert["winner"])
        self.assertTrue(check_certificate(formula, cert, env))

    def test_failure_counterstrategy(self) -> None:
        formula = self.false_contract()
        env = (4,)
        cert = canonical_certificate(formula, env)
        self.assertFalse(formula_value(formula, env))
        self.assertFalse(cert["winner"])
        self.assertTrue(check_certificate(formula, cert, env))

    def test_tampered_certificate_rejected(self) -> None:
        formula = self.true_contract()
        env = (3,)
        cert = canonical_certificate(formula, env)
        broken = copy.deepcopy(cert)
        broken["children"][1]["index"] = 999
        self.assertFalse(check_certificate(formula, broken, env))


class TraceTests(unittest.TestCase):
    def test_sum_trace(self) -> None:
        trace = TraceSystem(
            good=lambda n: n >= 0,
            init=lambda _n: 0,
            bound=lambda n: n,
            step=lambda i, state, _n: state + i + 1,
            invariant=lambda i, state, _n: state == i * (i + 1) // 2,
            accept=lambda state, n: state == n * (n + 1) // 2,
        )
        for n in range(20):
            self.assertTrue(trace.check(n))


class RelationalTests(unittest.TestCase):
    @staticmethod
    def machine() -> EvidenceMachine:
        # Choose three bits whose sum is two.  Several successful transcripts
        # exist; least-viable execution should select [0,1,1].
        return EvidenceMachine(
            start=lambda _x: 0,
            answer_bound=lambda _x, _r, _s: 2,
            halt=lambda _x, r, _s: r == 0,
            local=lambda _x, _r, _s, a: a in (0, 1),
            next_state=lambda _x, _r, s, a: s + a,
            post=lambda _x, _r, s: s == 2,
        )

    def test_viability_and_least_replay(self) -> None:
        machine = self.machine()
        self.assertTrue(machine.viability(0, 3))
        transcript, terminal, resource = machine.execute(0, 3)
        self.assertEqual(transcript, [0, 1, 1])
        self.assertEqual(terminal, 2)
        self.assertEqual(resource, 0)

    def test_nonviable_horizon(self) -> None:
        machine = self.machine()
        self.assertFalse(machine.viability(0, 1))
        with self.assertRaises(ValueError):
            machine.execute(0, 1)


class QuantitativeTests(unittest.TestCase):
    def test_error_dag(self) -> None:
        local = [Fraction(1, 16), Fraction(1, 32), Fraction(1, 64)]
        deps = [{}, {0: Fraction(2)}, {0: Fraction(1), 1: Fraction(3)}]
        budgets = propagate_error(local, deps)
        self.assertEqual(budgets[0], Fraction(1, 16))
        self.assertEqual(budgets[1], Fraction(5, 32))
        self.assertEqual(budgets[2], Fraction(35, 64))

    def test_dyadic_argmin(self) -> None:
        y, residual = dyadic_grid_argmin_residual(6)
        self.assertTrue(Fraction(0) <= y <= Fraction(2))
        self.assertLessEqual(residual, Fraction(4, 2**6))

    def test_height_enumeration(self) -> None:
        points = enumerate_integer_pairs(3, lambda x, y: x * x + y * y == 5)
        expected = {
            (-2, -1), (-2, 1), (-1, -2), (-1, 2),
            (1, -2), (1, 2), (2, -1), (2, 1),
        }
        self.assertEqual(set(points), expected)


class BarrierRegressionTests(unittest.TestCase):
    def test_metastable_windows(self) -> None:
        g = lambda n: n + 5
        for halt in (None, 0, 3, 5, 20):
            start = binary_metastable_window(halt, g)
            self.assertTrue(window_is_constant(halt, start, g))


if __name__ == "__main__":
    suite = unittest.defaultTestLoader.loadTestsFromModule(__import__(__name__))
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    if not result.wasSuccessful():
        raise SystemExit(1)
