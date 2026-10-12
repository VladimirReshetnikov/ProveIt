"""Resource boundaries around checked arithmetic and local pattern decisions."""
import importlib
import unittest
from unittest.mock import patch

from fastunknot import Diagram, recognize
from fastunknot.tangle_obstruction import recognize_with_subtangles


class RationalResourceTests(unittest.TestCase):
    def test_expiry_during_successful_certificate_verification(self):
        module = importlib.import_module("fastunknot.tangle_obstruction")
        diagram = Diagram.from_rational(0, ((0, 2), (0, 5), (-1, 3)))
        verified = [False]
        real_verify = module.verify_subtangle_certificate

        def verify(*args):
            result = real_verify(*args)
            verified[0] = True
            return result

        # The match is real, but its final verification consumes the deadline.
        with patch.object(module, "monotonic", side_effect=lambda: 2.0 if verified[0] else 0.0), \
                patch.object(module, "verify_subtangle_certificate", side_effect=verify):
            result = recognize_with_subtangles(diagram, seconds=1.0)
        self.assertTrue(verified[0])
        self.assertEqual((result.status, result.method), ("UNKNOWN", "resource-limit"))

    def test_wrapper_budget_and_stage_option_validation(self):
        diagram = Diagram.from_pd([])
        for seconds in (-1, True, float("inf"), float("nan"), "1"):
            with self.subTest(seconds=seconds), self.assertRaises(ValueError):
                recognize_with_subtangles(diagram, seconds=seconds)
        for value in (0, 1, None, "yes"):
            with self.subTest(value=value), self.assertRaises(ValueError):
                recognize(diagram, use_rational=value)
        # Empty catalogues and the zero-crossing case cannot evade the deadline.
        self.assertEqual(recognize_with_subtangles(diagram, patterns=[], seconds=0).status,
                         "UNKNOWN")


if __name__ == "__main__":
    unittest.main()
