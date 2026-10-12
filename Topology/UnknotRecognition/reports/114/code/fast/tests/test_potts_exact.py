"""Exact arithmetic and end-to-end soundness of the Potts filter options."""
import contextlib
import importlib
import io
import json
from pathlib import Path
import random
import unittest
from unittest.mock import patch

from fastunknot import Diagram
from fastunknot.__main__ import main
from fastunknot.filters import FilterLimit, PRIME
from fastunknot.potts import POTTS_X, potts_bracket
from fastunknot.potts_exact import (equal_spin, multiply, potts_exact,
                                   potts_exact_obstruction, power, x_power, witness_from_exact)
from fastunknot.scan import ScanLimit


PIPELINE = importlib.import_module("fastunknot.recognize")
EXAMPLES = Path(__file__).resolve().parents[1] / "examples"
FORCE_FILTER = dict(use_braid=False, use_seifert=False, use_reduction=False,
                    use_descending=False, use_factorization=False, use_alexander=False)


class ExactPottsTests(unittest.TestCase):
    def test_ring_identities_and_equal_spin_shortcuts(self):
        rng = random.Random(7113)
        for q in range(5, 10):
            self.assertEqual(multiply((0, 1), (q - 2, -1), q), (1, 0))
            self.assertEqual(power((1, 1), 2, q), (0, q))
            for _ in range(40):
                value = (rng.randrange(-100, 101), rng.randrange(-100, 101))
                for e in (-1, 1):
                    x = x_power(-e, q)
                    self.assertEqual(equal_spin(value, e, q),
                                     multiply(value, (-x[0], -x[1]), q))

    def test_quadratic_modular_reduction_on_named_examples(self):
        for path in sorted(EXAMPLES.glob("*.json")):
            diagram = Diagram.from_json(json.loads(path.read_text()))
            for shade in (0, 1):
                exact = potts_exact(diagram, colors=5, shade=shade,
                                    max_states=None, max_transitions=None)
                modular = potts_bracket(diagram, shade=shade,
                                        max_states=None, max_transitions=None)
                a, b = exact["partition_function"]
                self.assertEqual((a + b * POTTS_X) % PRIME,
                                 modular["partition_function"], path.name)
                self.assertEqual(exact["differs"],
                                 modular["bracket"] != modular["unknot_bracket"], path.name)

    def test_exact_five_color_blind_family_and_six_color_repair(self):
        for m in (1, 2, 4, 5, 7, 8, 11, 13, 17):
            diagram = Diagram.from_braid(3, [1, -2] * m)
            five = potts_exact(diagram, colors=5, order=list(range(2 * m)))
            six = potts_exact(diagram, colors=6, order=list(range(2 * m)))
            self.assertEqual(five["differs"], m % 2 == 0)
            self.assertEqual(six["differs"], m != 1)
            self.assertEqual(six["peak_states"], five["peak_states"])

    def test_mirrors_shading_and_unknot_examples(self):
        for name in ("hard_unknot_8", "grid_scrambled_unknot", "unknot_braid40", "unknot"):
            diagram = Diagram.from_json(json.loads((EXAMPLES / (name + ".json")).read_text()))
            for q in (5, 6, 7):
                for d in (diagram, diagram.mirror()):
                    for shade in (0, 1):
                        self.assertIsNone(potts_exact_obstruction(d, colors=q, shade=shade))

    def test_invalid_options(self):
        diagram = Diagram.from_braid(2, [1])
        for q in (4, -1, 5.0, True):
            with self.assertRaises(ValueError):
                potts_exact(diagram, colors=q)
        for name in ("max_states", "max_transitions"):
            for value in (-1, True, 0.25):
                with self.assertRaises(ValueError):
                    potts_exact(diagram, **{name: value})
            with self.assertRaises(FilterLimit):
                potts_exact(diagram, **{name: 0})
        self.assertFalse(potts_exact(Diagram.from_pd([]), max_states=0)["differs"])

    def test_exact_budget_boundary_and_callback(self):
        diagram = Diagram.from_braid(3, [1, -2] * 5)
        expected = potts_exact(diagram)
        self.assertEqual(potts_exact(diagram, max_transitions=expected["transitions"]), expected)
        with self.assertRaises(FilterLimit):
            potts_exact(diagram, max_transitions=expected["transitions"] - 1)
        with self.assertRaises(ScanLimit):
            potts_exact(diagram, check=lambda: (_ for _ in ()).throw(ScanLimit("test")))

    def test_pipeline_reports_witnesses_and_preserves_fallback(self):
        knotted = Diagram.from_pd(Diagram.from_braid(3, [1, -2] * 5).pd)
        result = PIPELINE.recognize(knotted, jones_backend="potts-exact", **FORCE_FILTER)
        self.assertEqual((result.status, result.method), ("KNOTTED", "jones-potts-exact"))
        self.assertEqual(result.evidence["jones"]["q"], 6)
        # Exact equality is never an unknot certificate: this q=5 blind case
        # proceeds to the independently retained Khovanov backend.
        result = PIPELINE.recognize(knotted, jones_backend="potts-exact",
                                    potts_colors=5, **FORCE_FILTER)
        self.assertEqual(result.status, "KNOTTED")
        self.assertIn("khovanov", result.evidence)
        self.assertEqual(result.evidence["jones"], "inconclusive")

    def test_filter_exhaustion_is_not_a_knot_verdict(self):
        unknot = Diagram.from_json(json.loads((EXAMPLES / "hard_unknot_8.json").read_text()))
        for backend in ("potts5", "potts-exact", "potts-exact-factorized"):
            result = PIPELINE.recognize(unknot, jones_backend=backend,
                                        jones_max_states=0, **FORCE_FILTER)
            self.assertEqual(result.status, "UNKNOT")
            self.assertIn("skipped", result.evidence["jones"])
            self.assertIn("khovanov", result.evidence)

    def test_global_resource_limit_returns_unknown(self):
        diagram = Diagram.from_braid(2, [1, 1, 1])
        for backend in ("potts5", "potts-exact", "potts-exact-factorized"):
            result = PIPELINE.recognize(diagram, jones_backend=backend, seconds=0)
            self.assertEqual((result.status, result.method), ("UNKNOWN", "resource-limit"))

    def test_cli_budget_is_inconclusive_and_exact_q_is_honored(self):
        path = str(EXAMPLES / "trefoil.json")
        for backend in ("matching", "potts5", "potts-exact", "potts-exact-factorized"):
            stream = io.StringIO()
            with contextlib.redirect_stdout(stream):
                code = main(["jones", path, "--backend", backend, "--max-transitions", "0"])
            self.assertEqual(code, 3)
            self.assertEqual(json.loads(stream.getvalue())["verdict"], "INCONCLUSIVE")
        stream = io.StringIO()
        with contextlib.redirect_stdout(stream):
            code = main(["jones", path, "--backend", "potts-exact", "--potts-colors", "7"])
        self.assertEqual(code, 0)
        self.assertEqual(json.loads(stream.getvalue())["witness"]["q"], 7)

    def test_pipeline_invalid_backend_and_color_count(self):
        for options in ({"jones_backend": "wrong"}, {"potts_colors": 4},
                        {"jones_max_states": -1}, {"jones_max_transitions": True}):
            with self.assertRaises(ValueError):
                PIPELINE.recognize(Diagram.from_pd([]), **options)

    def test_large_integer_witness_is_json_safe_and_uses_pair_inequality(self):
        huge = 1 << 20000
        raw = dict(partition_function=[huge, -huge], unknot_partition=[1, 0], differs=False)
        witness = witness_from_exact(raw)
        encoded = json.loads(json.dumps(witness))
        self.assertTrue(encoded["differs"])
        self.assertEqual([int(x, 16) for x in encoded["partition_function_hex"]], [huge, -huge])
        self.assertEqual(raw["partition_function"], [huge, -huge])
        self.assertIsNone(witness_from_exact(dict(partition_function=[1, 0],
                                                 unknot_partition=[1, 0], differs=True)))

    def test_factorized_exact_pipeline_and_cli(self):
        diagram = Diagram.from_pd(Diagram.from_braid(3, [1, -2] * 5).pd)
        result = PIPELINE.recognize(diagram, jones_backend="potts-exact-factorized", **FORCE_FILTER)
        self.assertEqual((result.status, result.method), ("KNOTTED", "jones-potts-exact-factorized"))
        evidence = json.loads(json.dumps(result.evidence))["jones"]
        self.assertNotEqual(evidence["partition_function_hex"], evidence["unknot_partition_hex"])
        result = PIPELINE.recognize(diagram, jones_backend="potts-exact-factorized",
                                    potts_colors=5, **FORCE_FILTER)
        self.assertEqual(result.status, "KNOTTED")
        self.assertIn("khovanov", result.evidence)
        stream = io.StringIO()
        with contextlib.redirect_stdout(stream):
            code = main(["jones", str(EXAMPLES / "trefoil.json"), "--backend",
                         "potts-exact-factorized"])
        self.assertEqual(code, 0)
        self.assertEqual(json.loads(stream.getvalue())["witness"]["q"], 6)


if __name__ == "__main__":
    unittest.main()
