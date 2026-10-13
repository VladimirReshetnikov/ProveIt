"""Pipeline, CLI, and resource behavior of opt-in component contraction."""
import contextlib
import io
import json
from pathlib import Path
import unittest

from fastunknot import Diagram, khovanov_rank, recognize
from fastunknot.__main__ import main

ROOT = Path(__file__).resolve().parents[1]
SCAN_ONLY = dict(use_braid=False, use_seifert=False, use_reduction=False,
                 use_descending=False, use_alexander=False, use_jones=False,
                 use_factorization=False)


class CompositionIntegrationTests(unittest.TestCase):
    def test_pipeline_evidence_and_rank_degrees(self):
        for name in ("conway", "hard_unknot_8"):
            diagram = Diagram.from_json(json.loads((ROOT / "examples" / (name + ".json")).read_text()))
            baseline = khovanov_rank(diagram.pd)
            for mode in ("component", "component-dense"):
                ranks = khovanov_rank(diagram.pd, composition=mode, check_d_squared=True)
                self.assertEqual(ranks["by_degree"], baseline["by_degree"])
                self.assertEqual(ranks["rank"], baseline["rank"])
                result = recognize(diagram, composition=mode, **SCAN_ONLY)
                self.assertEqual(result.status, "UNKNOT" if baseline["reduced_rank"] == 1 else "KNOTTED")
                self.assertEqual(result.evidence["khovanov"]["composition"], mode)
                self.assertIn("factored_calls", result.evidence["khovanov"]["composition_stats"])

    def test_allocation_limit_is_unknown_in_recognition(self):
        diagram = Diagram.from_json(json.loads((ROOT / "examples/conway.json").read_text()))
        result = recognize(diagram, composition="component-dense", composition_max_variables=0, **SCAN_ONLY)
        self.assertEqual((result.status, result.method), ("UNKNOWN", "resource-limit"))
        self.assertIn("variable limit", result.evidence["reason"])
        with self.assertRaises(MemoryError):
            khovanov_rank(diagram.pd, composition="component-dense", composition_max_variables=0)

    def test_invalid_options_rejected_before_early_verdict(self):
        diagram = Diagram.from_pd([])
        for options in (dict(composition="guess"), dict(composition_max_variables=-1),
                        dict(composition="component", race=2),
                        dict(composition="component", algebra="sets"),
                        dict(composition="component", pivot="lifo")):
            with self.assertRaises(ValueError):
                recognize(diagram, **options)
            with self.assertRaises(ValueError):
                khovanov_rank(diagram.pd, **options)
        with self.assertRaises(ValueError):
            recognize(diagram, composition="component", backend="shared")

    def test_cli_selection_and_resource_result(self):
        path = str(ROOT / "examples/conway.json")
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            code = main(["recognize", path, "--composition", "component-dense",
                         "--composition-max-variables", "0", "--no-seifert", "--no-braid",
                         "--no-reduction", "--no-descending", "--no-factor", "--no-alexander", "--no-jones"])
        self.assertEqual(code, 3)
        self.assertEqual(json.loads(out.getvalue())["status"], "UNKNOWN")
        self.assertEqual(err.getvalue(), "")
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = main(["khovanov", path, "--composition", "component-dense",
                         "--composition-max-variables", "0"])
        self.assertEqual(code, 3)
        self.assertEqual(json.loads(out.getvalue())["status"], "UNKNOWN")
        with contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(main(["khovanov", path, "--composition", "component", "--shared"]), 2)


if __name__ == "__main__":
    unittest.main()
