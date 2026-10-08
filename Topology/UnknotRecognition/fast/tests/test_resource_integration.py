"""Focused resource-limit regressions for preprocessing and factorization."""
import importlib
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from fastunknot import Diagram
from fastunknot.scan import ScanLimit

pipeline = importlib.import_module("fastunknot.recognize")


class RecognitionResourceTests(unittest.TestCase):
    def setUp(self):
        # These tests deliberately exercise stages after the structural filter.
        guard = patch.object(pipeline, "seifert_certificate", return_value=None)
        guard.start()
        self.addCleanup(guard.stop)

    @classmethod
    def setUpClass(cls):
        cls.diagram = Diagram.from_pd(Diagram.from_braid(3, [1, 1, 1, 2, 2, 2]).pd)

    def assert_unknown(self, result, message):
        self.assertEqual((result.status, result.method), ("UNKNOWN", "resource-limit"))
        self.assertEqual(result.input_crossings, self.diagram.crossings)
        self.assertIn(message, result.evidence["reason"])

    def test_zero_budget_stops_before_factorization(self):
        for backend, name in (("interlacement", "visible_factors_interlacement"),
                              ("legacy", "visible_factors")):
            with self.subTest(backend=backend), patch.object(pipeline, name) as factor:
                result = pipeline.recognize(self.diagram, seconds=0,
                                            use_reduction=False, use_descending=False,
                                            factor_backend=backend)
                self.assert_unknown(result, "time budget exhausted")
                factor.assert_not_called()

    def test_factorization_resource_exceptions_return_unknown(self):
        for backend, name in (("interlacement", "visible_factors_interlacement"),
                              ("legacy", "visible_factors")):
            for error in (ScanLimit("injected factor limit"), MemoryError("injected memory limit")):
                with self.subTest(backend=backend, error=type(error).__name__):
                    with patch.object(pipeline, name, side_effect=error) as factor:
                        result = pipeline.recognize(self.diagram, use_reduction=False,
                                                    use_descending=False, factor_backend=backend)
                    self.assert_unknown(result, str(error))
                    factor.assert_called_once()
                    self.assertTrue(callable(factor.call_args.kwargs["check"]))

    def test_preprocessing_resource_exceptions_return_unknown(self):
        for stage in ("simplify", "descending_start"):
            for error in (ScanLimit("injected preprocessing limit"),
                          MemoryError("injected preprocessing memory")):
                with self.subTest(stage=stage, error=type(error).__name__):
                    with patch.object(pipeline, stage, side_effect=error):
                        result = pipeline.recognize(self.diagram,
                                                    use_reduction=stage == "simplify",
                                                    use_descending=stage == "descending_start")
                    self.assert_unknown(result, str(error))

    def test_deadline_is_checked_after_coarse_simplification(self):
        clock = [0.0]

        def delayed_simplify(diagram, **options):
            clock[0] = 2.0
            return Diagram.from_pd([]), []

        with patch.object(pipeline, "monotonic", side_effect=lambda: clock[0]):
            with patch.object(pipeline, "simplify", side_effect=delayed_simplify):
                result = pipeline.recognize(self.diagram, seconds=1)
        self.assert_unknown(result, "time budget exhausted")

    def test_deadline_is_checked_after_descending_test(self):
        clock = [0.0]

        def delayed_descending(diagram):
            clock[0] = 2.0
            return 0

        with patch.object(pipeline, "monotonic", side_effect=lambda: clock[0]):
            with patch.object(pipeline, "descending_start", side_effect=delayed_descending):
                result = pipeline.recognize(self.diagram, seconds=1, use_reduction=False)
        self.assert_unknown(result, "time budget exhausted")

    def test_deadline_callback_reaches_each_factor_backend(self):
        for backend, name in (("interlacement", "visible_factors_interlacement"),
                              ("legacy", "visible_factors")):
            clock = [0.0]
            reached = []

            def delayed_factorization(diagram, check):
                clock[0] = 2.0
                reached.append(True)
                check()
                self.fail("factorization callback did not enforce its deadline")

            with self.subTest(backend=backend):
                with patch.object(pipeline, "monotonic", side_effect=lambda: clock[0]):
                    with patch.object(pipeline, name, side_effect=delayed_factorization):
                        result = pipeline.recognize(self.diagram, seconds=1,
                                                    use_reduction=False, use_descending=False,
                                                    factor_backend=backend)
                self.assert_unknown(result, "time budget exhausted")
                self.assertEqual(reached, [True])

    def test_deadline_is_checked_between_factor_decisions(self):
        clock = [0.0]

        def delayed_decision(diagram, evidence, **options):
            clock[0] = 2.0
            return "UNKNOT", "injected completed decision"

        with patch.object(pipeline, "monotonic", side_effect=lambda: clock[0]):
            with patch.object(pipeline, "_decide_prime_looking",
                              side_effect=delayed_decision) as decide:
                result = pipeline.recognize(self.diagram, seconds=1,
                                            use_reduction=False, use_descending=False)
        self.assert_unknown(result, "time budget exhausted")
        self.assertEqual(decide.call_count, 1)


if __name__ == "__main__":
    unittest.main()
