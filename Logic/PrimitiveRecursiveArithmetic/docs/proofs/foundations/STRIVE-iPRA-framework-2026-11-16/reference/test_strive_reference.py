from __future__ import annotations

import json
import random
import unittest
from pathlib import Path

from strive_reference import (
    StriveError,
    canonical_strategy,
    certificate_bound,
    check_strategy,
    decode_strategy,
    evaluate,
    formula_summary,
    least_demand_closure,
    mixed_digit,
    mixed_pack,
    mixed_unpack,
)


def v(name: str):
    return {"var": name}


def add(a, b):
    return {"add": [a, b]}


def mod(a, b):
    return {"mod": [a, b]}


def atom(predicate, label="atom"):
    return {"kind": "atom", "predicate": predicate, "label": label}


def exists(var, bound, body):
    return {"kind": "exists", "var": var, "bound": bound, "body": body}


def forall(var, bound, body):
    return {"kind": "forall", "var": var, "bound": bound, "body": body}


TRUE_CHALLENGE = forall(
    "q",
    4,
    exists(
        "z",
        4,
        forall(
            "e",
            3,
            atom(
                {"eq": [mod(add(v("z"), v("q")), 4), 0]},
                "(z+q) mod 4 = 0",
            ),
        ),
    ),
)

FALSE_CHALLENGE = forall(
    "q",
    3,
    exists(
        "z",
        2,
        forall(
            "e",
            2,
            atom({"lt": [v("q"), v("z")]}, "q < z"),
        ),
    ),
)


class MixedRadixTests(unittest.TestCase):
    def test_roundtrip(self):
        rng = random.Random(20261116)
        for _ in range(250):
            length = rng.randrange(0, 8)
            radices = [rng.randrange(1, 12) for _ in range(length)]
            digits = [rng.randrange(radix) for radix in radices]
            code = mixed_pack(digits, radices)
            self.assertEqual(mixed_unpack(code, radices), digits)
            for i, digit in enumerate(digits):
                self.assertEqual(mixed_digit(code, radices, i), digit)

    def test_empty_table(self):
        self.assertEqual(mixed_pack([], []), 0)
        self.assertEqual(mixed_unpack(0, []), [])

    def test_rejects_out_of_range(self):
        with self.assertRaises(StriveError):
            mixed_pack([2], [2])
        with self.assertRaises(StriveError):
            mixed_unpack(6, [2, 3])


class StrategyTests(unittest.TestCase):
    def assert_sound_exhaustively(self, formula):
        truth = evaluate(formula, {})
        for side in (False, True):
            bound = certificate_bound(formula, {}, side)
            # These examples are deliberately small enough for a complete scan.
            self.assertLess(bound, 20000)
            for code in range(bound):
                if check_strategy(formula, {}, side, code):
                    self.assertEqual(side, truth)
        side, code = canonical_strategy(formula, {})
        self.assertEqual(side, truth)
        self.assertTrue(check_strategy(formula, {}, side, code))
        self.assertLess(code, certificate_bound(formula, {}, side))

    def test_success_formula(self):
        self.assertTrue(evaluate(TRUE_CHALLENGE, {}))
        self.assert_sound_exhaustively(TRUE_CHALLENGE)
        summary = formula_summary(TRUE_CHALLENGE)
        self.assertTrue(summary["canonical_check"])
        self.assertEqual(summary["certificate"]["kind"], "forall")

    def test_failure_formula(self):
        self.assertFalse(evaluate(FALSE_CHALLENGE, {}))
        self.assert_sound_exhaustively(FALSE_CHALLENGE)
        side, code = canonical_strategy(FALSE_CHALLENGE)
        decoded = decode_strategy(FALSE_CHALLENGE, {}, side, code)
        self.assertFalse(side)
        self.assertEqual(decoded["kind"], "forall")
        self.assertEqual(decoded["choice"], 1)  # least counterchallenge q=1

    def test_empty_bounds(self):
        ex0 = exists("x", 0, atom(True, "true"))
        all0 = forall("x", 0, atom(False, "false"))
        self.assertFalse(evaluate(ex0))
        self.assertTrue(evaluate(all0))
        self.assertEqual(certificate_bound(ex0, {}, True), 0)
        self.assertEqual(certificate_bound(ex0, {}, False), 1)
        self.assertEqual(certificate_bound(all0, {}, True), 1)
        self.assertEqual(certificate_bound(all0, {}, False), 0)
        self.assert_sound_exhaustively(ex0)
        self.assert_sound_exhaustively(all0)

    def test_binary_connectives(self):
        formula = {
            "kind": "or",
            "left": {
                "kind": "and",
                "left": atom(True, "T"),
                "right": atom(False, "F"),
            },
            "right": atom(True, "T2"),
        }
        self.assert_sound_exhaustively(formula)

    def test_out_of_bound_code_rejected(self):
        side, _ = canonical_strategy(TRUE_CHALLENGE)
        bound = certificate_bound(TRUE_CHALLENGE, {}, side)
        self.assertFalse(check_strategy(TRUE_CHALLENGE, {}, side, bound))


class DemandClosureTests(unittest.TestCase):
    def test_cyclic_closure(self):
        caps = (3, 3, 4)

        def transfer(d):
            return (
                max(1, d[1]),
                min(3, d[0] + 1),
                max(2, d[0], d[1]),
            )

        result = least_demand_closure((0, 0, 0), caps, transfer)
        self.assertEqual(result.value, (3, 3, 3))
        self.assertLessEqual(len(result.trace) - 1, result.capacity_budget)
        self.assertEqual(
            tuple(max(x, y) for x, y in zip(result.value, transfer(result.value))),
            result.value,
        )

    def test_dimension_error(self):
        with self.assertRaises(StriveError):
            least_demand_closure((0,), (1, 2), lambda d: d)


class SerializationTests(unittest.TestCase):
    def test_summary_json(self):
        encoded = json.dumps(formula_summary(FALSE_CHALLENGE), sort_keys=True)
        self.assertIn("canonical_code", encoded)
        self.assertIn("certificate", encoded)


if __name__ == "__main__":
    unittest.main()
