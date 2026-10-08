"""Public API and CLI integration checks for the structural/compressed release."""
from __future__ import annotations

import json
from pathlib import Path
import random
import subprocess
import sys
import unittest

from fastunknot import Diagram, recognize, verify_seifert_certificate


EXAMPLES = Path(__file__).resolve().parents[1] / "examples"
SCAN_ONLY = dict(use_seifert=False, use_reduction=False, use_descending=False,
                 use_factorization=False, use_modular=False, use_jones=False,
                 use_alexander=False, use_r3=False)


def example(name):
    return Diagram.from_json(json.loads((EXAMPLES / (name + ".json")).read_text()))


class IntegrationTests(unittest.TestCase):
    def test_default_structural_certificates_are_replayable(self):
        cases = [(Diagram.from_pd([]), "UNKNOT"),
                 (Diagram.from_braid(4, [1, -2, 3]), "UNKNOT"),
                 (Diagram.from_braid(3, [1, -2] * 20), "KNOTTED"),
                 (Diagram.from_braid(5, [1, 2, 3, 4] * 7), "KNOTTED")]
        for diagram, status in cases:
            result = recognize(diagram)
            self.assertEqual(result.status, status)
            self.assertTrue(verify_seifert_certificate(
                diagram, result.evidence["seifert_certificate"]))
            self.assertEqual(recognize(diagram, use_seifert=False).status, status)
            self.assertFalse(result.to_json()["quasipolynomial_guarantee"])

    def test_backends_preserve_verdicts_and_evidence_semantics(self):
        for name, status in (("trefoil", "KNOTTED"), ("hard_unknot_8", "UNKNOT"),
                             ("conway", "KNOTTED"), ("conway_sum_2", "KNOTTED")):
            for backend in ("standard", "shared", "saturated", "euler"):
                with self.subTest(name=name, backend=backend):
                    result = recognize(example(name), backend=backend,
                                       check_d_squared=True, **SCAN_ONLY)
                    self.assertEqual(result.status, status)
                    evidence = result.evidence["khovanov"]
                    if backend in ("saturated", "euler"):
                        self.assertNotIn("rank", evidence)
                        self.assertNotIn("unreduced_rank", evidence)
                        self.assertNotIn("reduced_rank", evidence)
                        if "rank_capped" in evidence:
                            self.assertEqual(evidence["rank_capped"],
                                             2 if status == "UNKNOT" else 3)
                        else:
                            self.assertEqual(evidence["rank_lower_bound_capped"], 3)
                            self.assertEqual(status, "KNOTTED")

    def test_default_pipeline_matches_legacy_on_random_closures(self):
        rng = random.Random(2026100717)
        checked = 0
        while checked < 100:
            strands = rng.randrange(2, 5)
            word = [rng.choice((-1, 1)) * rng.randrange(1, strands)
                    for _ in range(rng.randrange(strands - 1, 12))]
            try:
                diagram = Diagram.from_braid(strands, word)
            except ValueError:
                continue
            new = recognize(diagram)
            old = recognize(diagram, use_seifert=False)
            self.assertEqual(new.status, old.status, word)
            if "seifert_certificate" in new.evidence:
                self.assertTrue(verify_seifert_certificate(
                    diagram, new.evidence["seifert_certificate"]))
            checked += 1

    def test_resource_limit_and_optional_inference_budget_differ(self):
        for backend in ("shared", "saturated", "euler"):
            result = recognize(example("conway"), backend=backend,
                               max_objects=1, **SCAN_ONLY)
            self.assertEqual(result.status, "UNKNOWN")
            self.assertEqual(result.method, "resource-limit")
        result = recognize(example("conway_sum_2"), backend="euler",
                           euler_max_states=0, **SCAN_ONLY)
        self.assertEqual(result.status, "KNOTTED")
        self.assertTrue(result.evidence["khovanov"]["euler_exhausted"])
        self.assertEqual(result.evidence["khovanov"]["rank_capped"], 3)

    def test_invalid_options_and_cli_rank_fields(self):
        diagram = example("trefoil")
        for options in ({"backend": "missing"}, {"backend": "shared", "tail": 1},
                        {"backend": "saturated", "algebra": "sets"},
                        {"backend": "euler", "race": 2},
                        {"euler_max_states": -1}, {"euler_max_states": True}):
            with self.assertRaises(ValueError):
                recognize(diagram, **options)
        command = [sys.executable, "-m", "fastunknot", "recognize",
                   str(EXAMPLES / "conway_sum_2.json"), "--no-seifert",
                   "--no-reduction", "--no-descending", "--no-factor",
                   "--no-alexander", "--no-jones", "--backend", "euler"]
        completed = subprocess.run(command, text=True, capture_output=True)
        self.assertEqual(completed.returncode, 0, completed.stderr)
        evidence = json.loads(completed.stdout)["evidence"]["khovanov"]
        self.assertEqual(evidence["rank_lower_bound_capped"], 3)
        self.assertNotIn("rank", evidence)
        self.assertNotIn("rank_capped", evidence)
        invalid = subprocess.run(command + ["--tail", "1"],
                                 text=True, capture_output=True)
        self.assertEqual(invalid.returncode, 2)
        self.assertNotIn("Traceback", invalid.stderr)


if __name__ == "__main__":
    unittest.main()
