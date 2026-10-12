"""Production degree convention, provenance, and twist resource contracts."""
import contextlib
import io
import json
from pathlib import Path
import random
import unittest
from unittest.mock import patch

from fastunknot import Diagram, DiagramError, ScanLimit, khovanov_rank, recognize
from fastunknot.__main__ import main
from fastunknot.twist import Budget, Run
from fastunknot.twist.core import recognize as recognize_runs
from fastunknot.twist_adapter import twist_khovanov_rank

ROOT = Path(__file__).resolve().parents[1]
SCAN_ONLY = dict(use_braid=False, use_seifert=False, use_reduction=False,
                 use_descending=False, use_factorization=False, use_alexander=False,
                 use_jones=False, use_r3=False)


class TwistIntegrationTests(unittest.TestCase):
    def test_random_braids_match_every_production_degree(self):
        rng = random.Random(2026100717)
        checked = 0
        while checked < 100:
            strands = rng.randrange(2, 6)
            word = [rng.choice((-1, 1))*rng.randrange(1, strands) for _ in range(rng.randrange(1, 11))]
            try:
                diagram = Diagram.from_braid(strands, word)
            except DiagramError:
                continue
            expected = khovanov_rank(diagram.pd, check_d_squared=True)
            actual = twist_khovanov_rank(diagram, check_d_squared=True)
            self.assertEqual(actual["by_degree"], expected["by_degree"], word)
            self.assertEqual(actual["rank"], expected["rank"], word)
            self.assertEqual(actual["preflight"]["exact_basis"], actual["stats"]["basis"])
            checked += 1

    def test_original_source_is_valid_after_whole_diagram_reduction(self):
        diagram = Diagram.from_braid(4, [1, -2, 1, -2, 3])
        result = recognize(diagram, backend="twist", **{**SCAN_ONLY, "use_reduction": True})
        self.assertEqual((result.status, result.method), ("KNOTTED", "twist-khovanov-F2"))
        self.assertEqual((result.input_crossings, result.reduced_crossings), (5, 4))
        kh = result.evidence["khovanov"]
        self.assertEqual(kh["source_crossings"], 5)
        self.assertEqual(kh["grading_diagram"], "original checked source braid")
        self.assertEqual(kh["unreduced_rank_by_cube_degree"], khovanov_rank(diagram.pd)["by_degree"])

    def test_source_is_never_reused_for_a_proper_factor(self):
        diagram = Diagram.from_braid(3, [1, 1, 1, 2, 2, 2])
        with patch("fastunknot.twist_adapter.twist_khovanov_rank", wraps=twist_khovanov_rank) as compute:
            result = recognize(diagram, backend="twist", **{**SCAN_ONLY, "use_factorization": True})
        compute.assert_called_once()
        self.assertIs(compute.call_args.args[0], diagram)
        self.assertEqual(result.status, "KNOTTED")
        self.assertIn("connected_sum_factorization", result.evidence)
        self.assertEqual(result.evidence["khovanov"]["reduced_rank"], 9)
        self.assertEqual(len(result.evidence["factors"]), 2)
        for factor in result.evidence["factors"]:
            self.assertEqual(factor["status"], "INCONCLUSIVE")
            self.assertIn("twist_deferred", factor)
            self.assertNotIn("khovanov", factor)

    def test_cheap_factor_obstruction_avoids_whole_twist_complex(self):
        diagram = Diagram.from_braid(3, [1, 1, 1, 2, 2, 2])
        with patch("fastunknot.twist_adapter.twist_khovanov_rank", side_effect=AssertionError("unneeded")):
            result = recognize(diagram, backend="twist",
                               **{**SCAN_ONLY, "use_factorization": True, "use_alexander": True})
        self.assertEqual(result.method, "connected-sum-factor:alexander-modular")

    def test_pd_falls_back_and_raw_twist_requires_provenance(self):
        diagram = Diagram.from_pd(Diagram.from_braid(3, [1, -2, 1, -2]).pd)
        with self.assertRaises(ValueError):
            twist_khovanov_rank(diagram)
        with patch("fastunknot.twist_adapter.twist_khovanov_rank", side_effect=AssertionError("no source")):
            result = recognize(diagram, backend="twist", **SCAN_ONLY)
        self.assertEqual(result.method, "reduced-khovanov-F2-scan")
        self.assertIn("twist_skipped", result.evidence)

    def test_existing_filters_precede_twist_assembly(self):
        diagram = Diagram.from_braid(2, [1, 1, 1])
        with patch("fastunknot.twist_adapter.twist_khovanov_rank", side_effect=AssertionError("unneeded complex")):
            self.assertEqual(recognize(diagram, backend="twist").status, "KNOTTED")
            self.assertEqual(recognize(diagram, backend="twist", use_braid=False).status, "KNOTTED")

    def test_exact_preflight_rejects_before_homology_allocation(self):
        diagram = Diagram.from_braid(2, [1, 1, 1])
        with patch("fastunknot.twist_adapter.homology", side_effect=AssertionError("allocated")):
            with self.assertRaisesRegex(ScanLimit, "exact preflight basis"):
                twist_khovanov_rank(diagram, budget=Budget(max_basis=2))
        result = recognize(diagram, backend="twist", twist_max_basis=2, **SCAN_ONLY)
        self.assertEqual((result.status, result.method), ("UNKNOWN", "resource-limit"))

    def test_preflight_time_is_part_of_the_same_budget(self):
        diagram = Diagram.from_braid(2, [1, 1, 1])
        clock = [0.0]

        def delayed(*args, **kwargs):
            self.assertTrue(callable(kwargs["check"]))
            clock[0] = 2.0
            return {"exact_basis": 5}

        with patch("fastunknot.twist_adapter.monotonic", side_effect=lambda: clock[0]):
            with patch("fastunknot.twist_adapter.basis_size", side_effect=delayed):
                with self.assertRaisesRegex(ScanLimit, "time budget"):
                    twist_khovanov_rank(diagram, budget=Budget(seconds=1))

    def test_large_encoded_counts_are_resource_failures_not_decimal_errors(self):
        huge = Run(1, 10**5000 + 1)
        self.assertEqual(recognize_runs(2, [huge], budget=Budget(max_states=10))["status"], "UNKNOWN")
        self.assertEqual(recognize_runs(2, [Run(1, 1)]*20001)["status"], "UNKNOWN")

    def test_long_single_block_has_bounded_degree_size(self):
        from fastunknot.twist import homology
        from fastunknot.twist.preflight import degree_profile
        for length in (3, 31, 301):
            profile = degree_profile(2, [Run(1, length)])
            result = homology(2, [Run(1, length)])
            self.assertEqual(result["reduced_rank"], length)
            for key in ("peak_chain_dimension", "matrix_bit_upper_bound", "rank_xor_bit_upper_bound"):
                self.assertEqual(result["stats"][key], profile[key])
            self.assertEqual(profile["peak_chain_dimension"], 2)
            self.assertEqual(profile["matrix_bit_upper_bound"], length+1)
            self.assertEqual(profile["rank_xor_bit_upper_bound"], length+1)

    def test_budget_validation_and_caller_budget_is_unchanged(self):
        diagram = Diagram.from_braid(2, [1])
        budget = Budget(seconds=5)
        self.assertEqual(twist_khovanov_rank(diagram, budget=budget)["reduced_rank"], 1)
        self.assertEqual(budget.seconds, 5)
        budget.max_basis = -1
        with self.assertRaises(ValueError):
            twist_khovanov_rank(diagram, budget=budget)
        with self.assertRaises(ValueError):
            recognize(diagram, backend="twist", twist_max_basis=-1)
        with self.assertRaises(ValueError):
            recognize(diagram, backend="twist", composition="component")

    def test_mirrored_source_matches_its_own_raw_grading(self):
        diagram = Diagram.from_braid(3, [1, 1, 1, -2]).mirror()
        self.assertEqual(twist_khovanov_rank(diagram)["by_degree"], khovanov_rank(diagram.pd)["by_degree"])

    def test_cli_rank_and_resource_paths(self):
        path = str(ROOT / "examples/trefoil.json")
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = main(["khovanov", path, "--twist", "--check-d2"])
        self.assertEqual(code, 0)
        self.assertEqual(json.loads(out.getvalue())["reduced_rank"], 3)
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = main(["khovanov", path, "--twist", "--twist-max-basis", "1"])
        self.assertEqual(code, 3)
        self.assertEqual(json.loads(out.getvalue())["status"], "UNKNOWN")
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = main(["recognize", path, "--backend", "twist", "--twist-max-basis", "1",
                         "--no-braid", "--no-seifert", "--no-reduction", "--no-descending",
                         "--no-factor", "--no-alexander", "--no-jones"])
        self.assertEqual(code, 3)
        self.assertEqual(json.loads(out.getvalue())["status"], "UNKNOWN")
        with contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(main(["khovanov", path, "--twist", "--shared"]), 2)


if __name__ == "__main__":
    unittest.main()
