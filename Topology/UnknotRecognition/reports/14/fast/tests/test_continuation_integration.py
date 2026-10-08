"""Exercise actual public routes and distinguish exact from decision results."""
import json
from pathlib import Path
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from fastunknot import Diagram, recognize


class TestContinuationIntegration(unittest.TestCase):
    def test_fallback_backends_and_dp(self):
        for name, expected in (("conway", "KNOTTED"), ("hard_unknot_8", "UNKNOT")):
            diagram = Diagram.from_json(json.loads((ROOT / "examples" / (name + ".json")).read_text()))
            for backend in ("barcode", "fitting", "standard"):
                result = recognize(
                    diagram, backend=backend, order_window=8,
                    use_seifert=False, use_reduction=False, use_descending=False,
                    use_factorization=False, use_alexander=False, use_jones=False,
                    check_d_squared=True)
                self.assertEqual(result.status, expected)
                self.assertIn("scan_order_optimization", result.evidence)
                if backend != "standard":
                    kh = result.evidence["khovanov"]
                    self.assertIn("rank_capped", kh)
                    self.assertNotIn("unreduced_rank", kh)
                    self.assertEqual(kh["length_cap"], 2)

    def test_object_ceiling_is_unknown(self):
        diagram = Diagram.from_json(json.loads((ROOT / "examples/conway.json").read_text()))
        for backend in ("barcode", "fitting"):
            result = recognize(
                diagram, backend=backend, max_objects=0,
                use_seifert=False, use_reduction=False, use_descending=False,
                use_factorization=False, use_alexander=False, use_jones=False)
            self.assertEqual(result.status, "UNKNOWN")

    def test_command_line_routes(self):
        exact = subprocess.run(
            [sys.executable, "-m", "fastunknot", "khovanov", "examples/conway.json", "--fitting"],
            cwd=ROOT, capture_output=True, text=True, check=True)
        self.assertIn("by_degree", json.loads(exact.stdout))
        decision = subprocess.run(
            [sys.executable, "-m", "fastunknot", "recognize", "examples/conway.json",
             "--backend", "fitting", "--order-window", "8", "--no-seifert",
             "--no-reduction", "--no-descending", "--no-factor", "--no-alexander", "--no-jones"],
            cwd=ROOT, capture_output=True, text=True, check=True)
        result = json.loads(decision.stdout)
        self.assertEqual(result["status"], "KNOTTED")
        self.assertFalse(result["quasipolynomial_guarantee"])
        invalid = subprocess.run(
            [sys.executable, "-m", "fastunknot", "khovanov", "examples/conway.json",
             "--barcode", "--fitting"], cwd=ROOT, capture_output=True, text=True)
        self.assertEqual(invalid.returncode, 2)


if __name__ == "__main__":
    unittest.main()
