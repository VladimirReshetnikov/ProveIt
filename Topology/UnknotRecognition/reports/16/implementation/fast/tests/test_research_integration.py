"""End-to-end checks for the optional dense kernel and finite-group filter."""
from __future__ import annotations

import importlib
import json
import os
import random
import subprocess
import sys
import unittest
from pathlib import Path
from unittest.mock import patch

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from fastunknot import Diagram, khovanov_rank, recognize, factored_khovanov_rank
from fastunknot.finite_quotient_check import verify_certificate
from fastunknot.ordering import best_scan_order
from fastunknot.scan_fast import FastScan


def load(name):
    return Diagram.from_json(json.loads((ROOT / "examples" / (name + ".json")).read_text()))


class DenseKernelIntegrationTests(unittest.TestCase):
    def test_default_is_lazy_and_legacy(self):
        code = ("import sys; from fastunknot.scan_fast import FastScan; scan=FastScan(); "
                "print(scan.composition, "
                "'fastunknot.dense_compose' in sys.modules, "
                "'fastunknot.finite_quotient' in sys.modules)")
        run = subprocess.run([sys.executable, "-c", code], cwd=ROOT, capture_output=True, text=True)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertEqual(run.stdout.strip(), "legacy False False")

    def test_fixed_order_modes_shape_cache_tail_and_d_squared(self):
        for name in ("trefoil", "conway", "kinoshita_terasaka", "hard_unknot_8", "torus_3_7"):
            d = load(name)
            order = best_scan_order(d.pd, min(d.crossings, 12))
            expected = khovanov_rank(d.pd, order=order, composition="legacy")
            for composition in ("adaptive", "dense"):
                for shape_cache, tail in ((False, 0), (True, 0), (True, 2)):
                    actual = khovanov_rank(d.pd, order=order, composition=composition,
                                           shape_cache=shape_cache, tail=tail, check_d_squared=True)
                    self.assertEqual((actual["rank"], actual["by_degree"]),
                                     (expected["rank"], expected["by_degree"]))
                    self.assertEqual(actual["order"], order)
                    self.assertEqual(actual["composition"], composition)
                    calls = actual["stats"]["dense_transfer_calls"] if composition == "dense" else (
                        actual["stats"]["sparse_transfer_calls"])
                    self.assertGreater(calls, 0)

    def test_random_complete_scans(self):
        rng = random.Random(20261007)
        count = 0
        while count < 16:
            word = [rng.choice((-2, -1, 1, 2)) for _ in range(rng.choice((4, 6, 8, 10)))]
            try:
                d = Diagram.from_braid(3, word)
            except ValueError:
                continue
            order = list(range(d.crossings))
            rng.shuffle(order)
            expected = khovanov_rank(d.pd, order=order)
            for composition in ("adaptive", "dense"):
                actual = khovanov_rank(d.pd, order=order, composition=composition,
                                       check_d_squared=True)
                self.assertEqual((actual["rank"], actual["by_degree"]),
                                 (expected["rank"], expected["by_degree"]))
            count += 1

    def test_factor_and_race_preserve_configuration(self):
        summed = load("conway_sum_2")
        legacy = factored_khovanov_rank(summed)
        for composition in ("adaptive", "dense"):
            result = factored_khovanov_rank(summed, composition=composition)
            self.assertEqual((result["rank"], result["by_degree"]),
                             (legacy["rank"], legacy["by_degree"]))
            self.assertIn("dense_transfer_calls", result["stats"])
        d = load("conway")
        order = best_scan_order(d.pd, 11)
        expected = khovanov_rank(d.pd, order=order)
        actual = khovanov_rank(d.pd, order=order, composition="dense", race=2,
                               race_after=0, shape_cache=True, check_d_squared=True)
        self.assertEqual((actual["rank"], actual["by_degree"]),
                         (expected["rank"], expected["by_degree"]))
        self.assertEqual(actual["composition"], "dense")

    def test_worker_and_cli_flags(self):
        d = load("conway")
        job = {"pd": d.pd, "order": best_scan_order(d.pd, 11), "composition": "dense",
               "shape_cache": True, "check_d_squared": True}
        run = subprocess.run([sys.executable, "-m", "fastunknot", "_scan"], cwd=ROOT,
                             input=json.dumps(job), capture_output=True, text=True)
        self.assertEqual(run.returncode, 0, run.stderr)
        worker = json.loads(run.stdout)
        self.assertEqual((worker["reduced_rank"], worker["composition"]), (33, "dense"))
        self.assertGreater(worker["stats"]["dense_transfer_calls"], 0)
        run = subprocess.run([sys.executable, "-m", "fastunknot", "khovanov",
                              str(ROOT / "examples/conway.json"), "--composition", "adaptive"],
                             cwd=ROOT, capture_output=True, text=True)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertEqual(json.loads(run.stdout)["composition"], "adaptive")

    def test_invalid_configuration_rejected(self):
        d = load("conway")
        with self.assertRaises(ValueError):
            FastScan(composition="typo")
        for options in ({"composition": "typo"}, {"composition": "dense", "algebra": "sets"},
                        {"composition": "adaptive", "pivot": "lifo"},
                        {"composition": "dense", "self_inverse": False}):
            with self.assertRaises(ValueError):
                khovanov_rank(d.pd, **options)
        run = subprocess.run([sys.executable, "-m", "fastunknot", "khovanov",
                              str(ROOT / "examples/conway.json"), "--composition", "dense",
                              "--algebra", "sets"], cwd=ROOT, capture_output=True, text=True)
        self.assertEqual(run.returncode, 2)
        self.assertIn("requires bits", run.stderr)


class FiniteQuotientIntegrationTests(unittest.TestCase):
    def test_default_off_and_existing_filters_first(self):
        d = load("conway")
        plain = recognize(d)
        self.assertEqual(plain.method, "jones-modular")
        self.assertNotIn("finite_quotient", plain.evidence)
        with patch("fastunknot.finite_quotient.find_a5_by_seeds",
                   side_effect=AssertionError("optional filter ran before existing filters")):
            result = recognize(d, quotient_max_assignments=5000)
            self.assertEqual(result.method, "jones-modular")
            result = recognize(load("torus_3_5"), quotient_max_assignments=5000)
            self.assertEqual(result.method, "alexander-modular")

    def test_witness_and_factor_witness_replay(self):
        for name in ("conway", "kinoshita_terasaka"):
            result = recognize(load(name), use_jones=False, quotient_max_assignments=5000,
                               quotient_seconds=1.0, composition="adaptive")
            self.assertEqual((result.status, result.method), ("KNOTTED", "finite-quotient-A5-seeds"))
            evidence = result.evidence["finite_quotient"]
            self.assertTrue(verify_certificate(evidence["diagram_pd"], evidence["certificate"])["valid"])
            self.assertNotIn("khovanov", result.evidence)
        result = recognize(load("conway_sum_2"), use_jones=False, quotient_max_assignments=5000,
                           quotient_seconds=1.0)
        self.assertEqual(result.method, "connected-sum-factor:finite-quotient-A5-seeds")
        evidence = result.evidence["factors"][0]["finite_quotient"]
        self.assertTrue(verify_certificate(evidence["diagram_pd"], evidence["certificate"])["valid"])

    def test_filter_failure_remains_inconclusive_and_falls_back(self):
        options = dict(use_reduction=False, use_descending=False, use_factorization=False,
                       use_alexander=False, use_jones=False, use_r3=False, quotient_seconds=1.0)
        result = recognize(load("conway"), quotient_max_assignments=1, max_objects=0, **options)
        self.assertEqual(result.status, "UNKNOWN")
        self.assertEqual(result.evidence["finite_quotient"]["status"], "INCONCLUSIVE")
        result = recognize(load("torus_3_7"), quotient_max_assignments=1000, max_objects=0, **options)
        self.assertEqual(result.status, "UNKNOWN")
        self.assertEqual(result.evidence["finite_quotient"]["reason"], "selected A5 palette exhausted")
        result = recognize(load("hard_unknot_8"), quotient_max_assignments=1000,
                           composition="dense", **options)
        self.assertEqual((result.status, result.method), ("UNKNOT", "reduced-khovanov-F2-scan"))
        self.assertEqual(result.evidence["finite_quotient"]["status"], "INCONCLUSIVE")
        self.assertEqual(result.evidence["khovanov"]["composition"], "dense")

    def test_shared_global_deadline_and_filter_cap(self):
        module = importlib.import_module("fastunknot.recognize")
        clock, calls = [100.0], []

        def fake_filter(diagram, **options):
            calls.append(options)
            clock[0] += 1
            return {"status": "INCONCLUSIVE", "reason": "time budget exhausted", "certificate": None}

        with patch.object(module, "monotonic", side_effect=lambda: clock[0]), \
                patch("fastunknot.finite_quotient.find_a5_by_seeds", side_effect=fake_filter), \
                patch.object(module, "khovanov_rank", side_effect=AssertionError("expired budget used")):
            result = recognize(load("conway"), seconds=0.05, quotient_seconds=0.2,
                               quotient_max_assignments=50, use_reduction=False,
                               use_descending=False, use_factorization=False,
                               use_alexander=False, use_jones=False)
        self.assertEqual(result.status, "UNKNOWN")
        self.assertEqual(len(calls), 1)
        self.assertAlmostEqual(calls[0]["seconds"], 0.05)
        self.assertEqual(calls[0]["max_assignments"], 50)

    def test_quotient_cli_and_invalid_budgets(self):
        run = subprocess.run([sys.executable, "-m", "fastunknot", "recognize",
                              str(ROOT / "examples/conway.json"), "--no-jones",
                              "--quotient-max-assignments", "5000", "--quotient-seconds", "1"],
                             cwd=ROOT, capture_output=True, text=True)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertEqual(json.loads(run.stdout)["method"], "finite-quotient-A5-seeds")
        for options in ({"quotient_max_assignments": -1}, {"quotient_seconds": -1},
                        {"quotient_seconds": float("nan")}, {"quotient_seconds": float("inf")}):
            with self.assertRaises(ValueError):
                recognize(load("conway"), **options)


if __name__ == "__main__":
    unittest.main(verbosity=2)
