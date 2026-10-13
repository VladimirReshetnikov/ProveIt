"""Public API and CLI contracts for the optional primary splitter."""
import json
from pathlib import Path
import subprocess
import sys
import unittest

from fastunknot import Diagram, khovanov_rank, recognize
from fastunknot.scalar_split import fitting_khovanov_rank


ROOT = Path(__file__).resolve().parents[1]
NO_FILTERS = dict(
    use_braid=False, use_seifert=False, use_reduction=False,
    use_descending=False, use_alexander=False, use_jones=False,
    use_factorization=False,
)


class PrimaryIntegrationTests(unittest.TestCase):
    def test_exact_rank_and_degree_agree_with_standard_scanner(self):
        for name in ("trefoil", "figure_eight", "hard_unknot_8", "conway"):
            with self.subTest(name=name):
                diagram = Diagram.from_json(json.loads(
                    (ROOT / "examples" / (name + ".json")).read_text()))
                reference = khovanov_rank(diagram.pd)
                result = fitting_khovanov_rank(
                    diagram.pd, fitting_primary=True, check_d_squared=True)
                self.assertEqual(result["rank"], reference["rank"])
                self.assertEqual(result["by_degree"], reference["by_degree"])
                self.assertEqual(result["backend"], "scalar-primary-interval-sharing")
                self.assertNotIn("rank_capped", result)

    def test_pipeline_capped_contract_and_exhaustion(self):
        for word in ([1], [1, 1, 1]):
            diagram = Diagram.from_braid(2, word)
            result = recognize(diagram, backend="primary", **NO_FILTERS)
            self.assertEqual(result.status, "UNKNOT" if len(word) == 1 else "KNOTTED")
            evidence = result.evidence["khovanov"]
            self.assertEqual(evidence["backend"], "scalar-primary-interval-decision")
            self.assertEqual(evidence["rank_capped"], 2 if len(word) == 1 else 3)
            self.assertNotIn("rank", evidence)
            self.assertNotIn("by_degree", evidence)
            for limit in (dict(max_objects=0), dict(seconds=0)):
                limited = recognize(diagram, backend="primary", **limit, **NO_FILTERS)
                self.assertEqual(limited.status, "UNKNOWN")

    def test_option_validation_precedes_early_certificate(self):
        diagram = Diagram.from_braid(2, [1])
        for options in (dict(reduction="adaptive"), dict(composition="component"),
                        dict(race=2), dict(tail=1), dict(algebra="sets")):
            with self.subTest(options=options), self.assertRaises(ValueError):
                recognize(diagram, backend="primary", **options)

    def test_cli_exact_and_incompatible_modes(self):
        data = json.dumps(dict(braid=dict(strands=2, word=[1, 1, 1])))
        command = [sys.executable, "-B", "-m", "fastunknot", "khovanov", "-", "--primary"]
        result = subprocess.run(command, input=data, text=True, capture_output=True, cwd=ROOT)
        self.assertEqual(result.returncode, 0, result.stderr)
        decoded = json.loads(result.stdout)
        self.assertEqual(decoded["rank"], 6)
        self.assertEqual(decoded["backend"], "scalar-primary-interval-sharing")
        for option in ("--fitting", "--barcode", "--shared", "--twist", "--factor",
                       "--reduction=adaptive", "--composition=component"):
            with self.subTest(option=option):
                invalid = subprocess.run(command + [option], input=data, text=True,
                                         capture_output=True, cwd=ROOT)
                self.assertEqual(invalid.returncode, 2, invalid.stdout + invalid.stderr)

    def test_cli_primary_recognition(self):
        data = json.dumps(dict(braid=dict(strands=2, word=[1, 1, 1])))
        command = [sys.executable, "-B", "-m", "fastunknot", "recognize", "-",
                   "--backend", "primary", "--no-braid", "--no-seifert", "--no-reduction",
                   "--no-descending", "--no-alexander", "--no-jones", "--no-factor"]
        result = subprocess.run(command, input=data, text=True, capture_output=True, cwd=ROOT)
        self.assertEqual(result.returncode, 0, result.stderr)
        decoded = json.loads(result.stdout)
        self.assertEqual(decoded["status"], "KNOTTED")
        self.assertEqual(decoded["evidence"]["khovanov"]["backend"],
                         "scalar-primary-interval-decision")


if __name__ == "__main__":
    unittest.main()
