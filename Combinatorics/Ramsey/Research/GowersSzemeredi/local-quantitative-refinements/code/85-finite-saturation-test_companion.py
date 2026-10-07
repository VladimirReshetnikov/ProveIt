#!/usr/bin/env python3
"""Regression tests, including tamper rejection with python -O enabled."""
from __future__ import annotations

import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
HERE = Path(__file__).absolute().parents[1] / "companion"
SCRIPT = HERE / "classify.py"


class ClassifierRegressionTests(unittest.TestCase):
    def invoke(self, *args: str, optimized: bool = False) -> subprocess.CompletedProcess:
        command = [sys.executable, "-I", "-B", "-X", "int_max_str_digits=640"]
        if optimized:
            command.append("-O")
        command.extend([str(SCRIPT), *args])
        return subprocess.run(command, text=True, capture_output=True, check=False, timeout=30)

    def test_original_certificates_verify_both_modes(self) -> None:
        for optimized in (False, True):
            with self.subTest(optimized=optimized):
                result = self.invoke("--verify", str(HERE), optimized=optimized)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn("exactly 77", result.stdout)

    def test_generated_files_match_committed_files(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            result = self.invoke("--write", directory)
            self.assertEqual(result.returncode, 0, result.stderr)
            for name in ("compact_certificate.json", "finite_certificate.json"):
                self.assertEqual((Path(directory) / name).read_bytes(), (HERE / name).read_bytes())

    def test_corruption_rejected_both_modes_for_both_certificates(self) -> None:
        for filename in ("compact_certificate.json", "finite_certificate.json"):
            for optimized in (False, True):
                with self.subTest(filename=filename, optimized=optimized):
                    with tempfile.TemporaryDirectory() as directory:
                        target = Path(directory)
                        for name in ("compact_certificate.json", "finite_certificate.json"):
                            (target / name).write_bytes((HERE / name).read_bytes())
                        data = json.loads((target / filename).read_text())
                        if filename == "compact_certificate.json":
                            data["rows"][0]["first_loser"]["gap"] += 1
                        else:
                            data["rows"][0]["W"] += 1
                        (target / filename).write_text(
                            json.dumps(data, sort_keys=True, separators=(",", ":")) + "\n"
                        )
                        original_corrupt_bytes = (target / filename).read_bytes()
                        result = self.invoke("--verify", directory, optimized=optimized)
                        self.assertNotEqual(result.returncode, 0)
                        self.assertIn(f"certificate differs: {filename}", result.stderr)
                        self.assertEqual((target / filename).read_bytes(), original_corrupt_bytes)

    def test_write_and_verify_cannot_be_combined(self) -> None:
        for optimized in (False, True):
            with self.subTest(optimized=optimized):
                result = self.invoke("--write", str(HERE), "--verify", str(HERE), optimized=optimized)
                self.assertEqual(result.returncode, 2)
                self.assertIn("not allowed with argument", result.stderr)

    def test_missing_certificates_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            result = self.invoke("--verify", directory)
            self.assertNotEqual(result.returncode, 0)


class MathematicalRegressionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        import importlib.util
        spec = importlib.util.spec_from_file_location("classifier", SCRIPT)
        cls.c = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(cls.c)

    def test_displayed_example_gaps(self):
        self.assertEqual(self.c.W(27, 3) - self.c.W(27, 2), 10582)
        self.assertEqual(self.c.W(81, 7) - self.c.W(81, 8), 13515678)

    def test_clipping_and_representative_candidates(self):
        for n in range(3, 11): self.assertEqual(self.c.candidates(n), [1])
        for n, expected in ((11, [1, 2]), (27, [2, 3]), (81, [7, 8]), (583, [53, 54])):
            self.assertEqual(self.c.candidates(n), expected)

    def test_candidate_domain_rejection(self):
        for n in (0, 1, 2):
            with self.assertRaises(ValueError): self.c.candidates(n)
        for n, m in ((5, -1), (5, 3)):
            with self.assertRaises(ValueError): self.c.less_than_npstar(n, m)

    def test_exact_counts_and_maximum(self):
        data = self.c.exhaustive_certificate()
        self.assertEqual(data["orders_checked"], 1184)
        self.assertEqual(data["branches_checked"], 351648)
        self.assertEqual(len(data["saturating"]), 77)
        self.assertEqual(data["saturating"][-1], [583, 53, 11])
        self.assertEqual(data["ties"], [])
        self.assertIsNone(data["rows"][0]["gap_to_every_other_branch"])

    def test_twenty_seven_nontrivial_compact_gaps(self):
        rows = self.c.compact_certificate()["rows"]
        self.assertEqual(len(rows), 19)
        count = sum("gap" in r.get("last_winner", {}) for r in rows) + len(rows)
        self.assertEqual(count, 27)
        self.assertEqual(sum(r["last_winning_m"] for r in rows), 77)

    def test_runtime_guards_survive_optimization(self):
        import ast
        tree = ast.parse(SCRIPT.read_text())
        self.assertFalse(any(isinstance(n, ast.Assert) for n in ast.walk(tree)))
        self.assertFalse(any(isinstance(n, ast.Constant) and isinstance(n.value, float) for n in ast.walk(tree)))
        with self.assertRaises(ValueError): self.c.require(False, "sentinel")

    def test_read_only_wrapper_and_equal_mode_stdout(self):
        def inventory():
            return {p.name: p.read_bytes() for p in HERE.iterdir() if p.is_file()}
        before = inventory(); outputs = []
        for flags in ([], ["-O"]):
            r = subprocess.run([sys.executable, "-I", "-B", *flags, str(HERE / "exact_checks.py")],
                capture_output=True, timeout=30, check=False)
            self.assertEqual(r.returncode, 0, r.stderr)
            outputs.append(r.stdout)
        self.assertEqual(outputs[0], outputs[1]); self.assertEqual(inventory(), before)
        self.assertIn(b"rational support order and indicator attainment", outputs[0])

    def test_wrapper_refuses_arguments(self):
        r = subprocess.run([sys.executable, "-I", "-B", str(HERE / "exact_checks.py"), "--write"],
            capture_output=True, timeout=30, check=False)
        self.assertNotEqual(r.returncode, 0)

    def test_rational_support_candidates(self):
        from math import isqrt
        inner = [q for q in self.c.MAXIMA if (q-1) % 3 == 0 and isqrt((q-1)//3)**2 == (q-1)//3]
        self.assertEqual(inner, [4, 13])
        outer = [q for q in inner if isqrt(q*isqrt((q-1)//3)-(q-1))**2 == q*isqrt((q-1)//3)-(q-1)]
        self.assertEqual(outer, [4])


if __name__ == "__main__":
    unittest.main(verbosity=2)
