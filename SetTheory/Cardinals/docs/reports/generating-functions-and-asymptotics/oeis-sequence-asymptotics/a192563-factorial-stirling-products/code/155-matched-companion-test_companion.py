"""Regression, mathematical cross-check, boundary, and safe-I/O tests.

Run both: python -B -m unittest -v test_companion
          python -O -B -m unittest -v test_companion
"""
from __future__ import annotations

from fractions import Fraction as Q
import hashlib
import json
from math import factorial
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import fock_exact as f
import safe_io as io

HERE = Path(__file__).absolute().parent
EXPECTED_A = ["1", "-1/6", "55/72", "1381/6480", "76541/155520",
              "1807553/6531840", "385303949/1175731200", "-66416099/7054387200",
              "108926247893/338610585600", "-584017596861539/1005673439232000",
              "108854736210330631/84476568895488000"]
EXPECTED_H = ["1", "0", "3/4", "1/3", "155/288", "259/720", "2183/5760",
              "2809/60480", "3129727/9676800", "-3827969/7257600", "138901163/116121600"]
EXPECTED_E = ["1", "-1/6", "1/72", "31/6480", "-139/155520", "-9871/6531840",
              "324179/1175731200", "8225671/7054387200", "-69685339/338610585600",
              "-1674981058019/1005673439232000", "24279707153761/84476568895488000"]


class Coefficients(unittest.TestCase):
    def test_expected_coefficients_through_A10(self):
        data = f.coefficient_data(10)
        self.assertEqual(data["A"], list(map(Q, EXPECTED_A)))
        self.assertEqual(data["H"], list(map(Q, EXPECTED_H)))
        self.assertEqual(data["E"], list(map(Q, EXPECTED_E)))

    def test_bernoulli_convention_and_first_polynomials(self):
        self.assertEqual(f.bernoulli_numbers(6), list(map(Q, ["1", "-1/2", "1/6", "0", "-1/30", "0", "1/42"])))
        data = f.coefficient_data(3)
        self.assertEqual(data["g"][1], list(map(Q, ["0", "1/2", "-1/2"])))
        self.assertEqual(data["p"][3], list(map(Q, ["0", "0", "-1/24", "1/48", "1/16", "-1/48", "-1/48"])))

    def test_formal_exponential_by_independent_partition_product(self):
        # exp(sum g_m x^m) = product_m sum_j g_m^j x^(mj)/j!.
        data = f.coefficient_data(7)
        out = [[Q(1)]] + [[Q(0)] for _ in range(7)]
        for m in range(1, 8):
            factor = [[Q(0)] for _ in range(8)]
            power = [Q(1)]
            for j in range(8 // m + 1):
                if m * j > 7:
                    break
                factor[m * j] = f.poly_scale(power, Q(1, factorial(j)))
                power = f.poly_mul(power, data["g"][m])
            updated = [[Q(0)] for _ in range(8)]
            for r in range(8):
                for j in range(r + 1):
                    updated[r] = f.poly_add(updated[r], f.poly_mul(out[j], factor[r - j]))
            out = updated
        self.assertEqual(out, data["p"])

    def test_zero_order_and_bounds(self):
        self.assertEqual(f.coefficient_data(0)["A"], [Q(1)])
        for value in (-1, 11, True, "10", Q(10), 10.0):
            with self.subTest(value=value), self.assertRaises(io.InputError):
                f.coefficient_data(value)

    def test_committed_coefficients_match_generation(self):
        saved = json.loads((HERE / "results/coefficients_A10.json").read_text())
        self.assertEqual(saved, f.coefficient_document(10))


class Certificate(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.spec = dict(f.DEFAULT_SPEC)
        cls.result = f.certificate_bounds(cls.spec)

    def test_demo_unique_exact_integer(self):
        r = self.result
        self.assertEqual(r["exact"], 1273270076895432)
        self.assertLessEqual(r["lower"], r["exact"])
        self.assertLessEqual(r["exact"], r["upper"])
        self.assertEqual(f.ceil_q(r["lower"]), r["exact"])
        self.assertEqual(f.floor_q(r["upper"]), r["exact"])
        self.assertLess(r["upper"] - r["lower"], Q(2283679986302, 10 ** 30))

    def test_upper_center_and_universal_q(self):
        r = self.result
        self.assertEqual(r["center"], r["root_upper"])
        self.assertLessEqual(r["d"], 0)
        self.assertEqual(r["q"], Q(80, 81))
        self.assertLess(r["S2"], r["q"])
        self.assertEqual(r["root_upper"] - r["root_lower"], Q(10, 2 ** 48))
        for n in range(1, 21):
            low, high = f.upper_saddle_center(n, 8)
            self.assertGreaterEqual(f.saddle_residual(n, low), 0)
            self.assertLessEqual(f.saddle_residual(n, high), 0)
            s = sum((Q(1) / (j + high) ** 2 for j in range(1, n + 1)), Q(0))
            self.assertLess(s, Q(2, 3))

    def test_small_cases_and_K2(self):
        for n in range(1, 6):
            with self.subTest(n=n):
                r = f.certificate_bounds({"n": n, "K": 2, "bisections": 8, "exp_terms": 16})
                self.assertLessEqual(r["lower"], f.stirling_count(n))
                self.assertGreaterEqual(r["upper"], f.stirling_count(n))

    def test_n_zero(self):
        d = f.certificate_document({"n": 0, "K": 2, "bisections": 8, "exp_terms": 16})
        self.assertTrue(d["n_zero_special_case"])
        self.assertEqual(f.decode_rational(d["interval"]["lower"]), Q(1))
        self.assertEqual(f.decode_rational(d["interval"]["upper"]), Q(1))
        self.assertEqual(d["integer_decision"]["unique_integer"], "1")

    def test_committed_demo_exact_replay(self):
        saved = json.loads((HERE / "results/certificate_n10.json").read_text())
        for key in ("lower", "upper"):
            self.assertEqual(f.decode_rational(saved["interval"][key]), self.result[key])
        self.assertEqual(f.decode_rational(saved["interval"]["width"]),
                         self.result["upper"] - self.result["lower"])
        self.assertEqual(saved["inputs"], self.spec)

    def test_outward_decimals(self):
        for value in (Q(-101, 99), Q(-1, 3), Q(0), Q(1, 7), self.result["lower"]):
            low = Q(f.decimal_bound(value, 30))
            high = Q(f.decimal_bound(value, 30, upper=True))
            self.assertLessEqual(low, value)
            self.assertLessEqual(value, high)
            self.assertLessEqual(high - low, Q(1, 10 ** 30))

    def test_equality_is_not_an_unjustified_interval_decision(self):
        r = self.result
        self.assertEqual(f.compare_threshold(r["lower"], r["upper"], r["exact"]), "undecided")
        self.assertEqual(f.compare_threshold(r["lower"], r["upper"], r["exact"], r["exact"]), "equal")
        self.assertEqual(f.compare_threshold(r["lower"], r["upper"], r["exact"] + 1), "strictly_below")
        self.assertEqual(f.compare_threshold(r["lower"], r["upper"], r["exact"] - 1), "strictly_above")
        self.assertEqual(f.compare_threshold(Q(1), Q(1), 1), "undecided")
        with self.assertRaises(io.InputError):
            f.compare_threshold(Q(0), Q(1), 1, 2)

    def test_spec_validation_all_limits(self):
        bad = [None, [], {}, {**self.spec, "extra": 1}]
        for key, values in {"n": [-1, 21, True, "10", 1.0],
                            "K": [1, 97, False], "bisections": [7, 65],
                            "exp_terms": [15, 193]}.items():
            bad.extend({**self.spec, key: value} for value in values)
        for spec in bad:
            with self.subTest(spec=spec), self.assertRaises(io.InputError):
                f.certificate_bounds(spec)


class Arithmetic(unittest.TestCase):
    def test_stirling_matches_polynomial_product(self):
        for n in range(13):
            # Product prod_{j=1}^n(z+j) has coefficients [n+1,k+1].
            poly = [1]
            for j in range(1, n + 1):
                out = [0] * (len(poly) + 1)
                for k, a in enumerate(poly):
                    out[k] += j * a
                    out[k + 1] += a
                poly = out
            independent = sum(factorial(k) * x * x for k, x in enumerate(poly))
            self.assertEqual(independent, f.stirling_count(n))
        self.assertEqual([f.stirling_count(n) for n in range(5)], [1, 2, 15, 235, 6150])

    def test_enumeration_input_bounds(self):
        for n in (-1, 1001, True, 1.0, "2"):
            with self.assertRaises(io.InputError):
                f.stirling_count(n)

    def test_exact_exponential_bounds(self):
        self.assertEqual(f.exp_bounds(Q(0), 16), (Q(1), Q(1)))
        for x in (Q(1, 100), Q(1), Q(3), Q(10)):
            low, high = f.exp_bounds(x, 16)
            refined_low, refined_high = f.exp_bounds(x, 80)
            self.assertLessEqual(low, refined_low)
            self.assertLessEqual(refined_low, refined_high)
            self.assertLessEqual(refined_high, high)
            self.assertEqual(f.exp_bounds(-x, 16), (1 / high, 1 / low))
        for x, m in ((Q(18), 16), (Q(65), 100), (Q(1), 15), (Q(1), 193), (1.0, 16)):
            with self.assertRaises(io.InputError):
                f.exp_bounds(x, m)

    def test_big_integer_roundtrip_without_setting_changes(self):
        before = sys.get_int_max_str_digits()
        value = Q(10 ** 10000 + 3, 7)
        self.assertEqual(f.decode_rational(f.rational_json(value)), value)
        self.assertEqual(before, sys.get_int_max_str_digits())

    def test_invalid_rational_payloads(self):
        for payload in ({}, {"numerator": "01", "denominator": "1"},
                        {"numerator": "-0", "denominator": "1"},
                        {"numerator": "2", "denominator": "2"},
                        {"numerator": "1", "denominator": "0"},
                        {"numerator": "1", "denominator": "-1"},
                        {"numerator": "1.1", "denominator": "1"}):
            with self.subTest(payload=payload), self.assertRaises(io.InputError):
                f.decode_rational(payload)


class SafeIO(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)

    def tearDown(self):
        self.temp.cleanup()

    def test_fresh_output_and_refusal_to_overwrite(self):
        path = self.root / "fresh.json"
        io.write_new_json(path, {"ok": True})
        original = path.read_bytes()
        self.assertEqual(io.read_json(path), {"ok": True})
        with self.assertRaises(io.InputError):
            io.write_new_json(path, {"changed": True})
        self.assertEqual(path.read_bytes(), original)
        self.assertEqual(sorted(p.name for p in self.root.iterdir()), ["fresh.json"])

    def test_existing_directory_fifo_and_symlink_outputs_refused(self):
        target = self.root / "target.json"
        target.write_text("unchanged")
        targets = [self.root / "folder.json", self.root / "pipe.json",
                   self.root / "link.json", self.root / "dangling.json"]
        targets[0].mkdir()
        os.mkfifo(targets[1])
        targets[2].symlink_to(target)
        targets[3].symlink_to(self.root / "absent")
        for path in targets:
            with self.subTest(path=path), self.assertRaises(io.InputError):
                io.write_new_json(path, {})
        self.assertEqual(target.read_text(), "unchanged")
        self.assertFalse((self.root / "absent").exists())

    def test_parent_symlink_and_traversal_refused_for_input_and_output(self):
        real = self.root / "real"
        real.mkdir()
        source = real / "source.json"
        source.write_text("{}")
        link = self.root / "linked"
        link.symlink_to(real, target_is_directory=True)
        for action in (lambda: io.read_json(link / "source.json"),
                       lambda: io.write_new_json(link / "out.json", {}),
                       lambda: io.read_json(str(real) + "/../real/source.json"),
                       lambda: io.write_new_json(str(real) + "/../out.json", {}),
                       lambda: io.write_new_json(str(real) + "/./out.json", {})):
            with self.assertRaises(io.InputError):
                action()
        self.assertEqual(sorted(p.name for p in real.iterdir()), ["source.json"])

    def test_invalid_json_and_nonregular_input_refused(self):
        source = self.root / "input.json"
        cases = [b'{"n":1,"n":2}', b'{"n":1.0}', b'{"n":NaN}', b'{"n":Infinity}',
                 b'{"n":1234567890123}', b'not json', b'\xff', b'{}' + b' ' * 16384,
                 b'[' * 1500 + b']' * 1500]
        for payload in cases:
            source.write_bytes(payload)
            with self.subTest(payload=payload[:30]), self.assertRaises(io.InputError):
                io.read_json(source)
        link = self.root / "link.json"
        link.symlink_to(source)
        fifo = self.root / "fifo.json"
        os.mkfifo(fifo)
        for path in (link, fifo, self.root):
            with self.assertRaises(io.InputError):
                io.read_json(path)

    def test_bad_paths_suffix_and_absent_parent(self):
        for path in ("", ".", "..", "out\\name.json", "a\x00b", "a//b.json", str(self.root) + "/"):
            with self.subTest(path=path), self.assertRaises(io.InputError):
                io.write_new_json(path, {})
        for path in (self.root / "out.txt", self.root / "absent" / "out.json"):
            with self.assertRaises(io.InputError):
                io.write_new_json(path, {})

    def test_failed_publish_leaves_no_partial_output(self):
        path = self.root / "out.json"
        with patch.object(os, "link", side_effect=OSError("simulated failure")):
            with self.assertRaises(io.InputError):
                io.write_new_json(path, {"test": 1})
        self.assertFalse(path.exists())
        self.assertEqual(list(self.root.iterdir()), [])

    def test_output_size_bound(self):
        with self.assertRaises(io.InputError):
            io.write_new_json(self.root / "big.json", {"x": "x" * io.MAX_OUTPUT_BYTES})
        self.assertEqual(list(self.root.iterdir()), [])

    def run_cli(self, *args):
        flags = ["-O"] if sys.flags.optimize else []
        return subprocess.run([sys.executable, *flags, "-B", str(HERE / "fock_exact.py"), *args],
                              text=True, capture_output=True, timeout=30)

    def test_cli_n0_success_and_existing_output_refusal(self):
        output = self.root / "n0.json"
        args = ("certificate", "--input", str(HERE / "inputs/certificate_n0.json"),
                "--output", str(output))
        first = self.run_cli(*args)
        self.assertEqual(first.returncode, 0, first.stderr)
        original = output.read_bytes()
        second = self.run_cli(*args)
        self.assertEqual(second.returncode, 2)
        self.assertIn("already exists", second.stderr)
        self.assertEqual(output.read_bytes(), original)

    def test_cli_malformed_and_out_of_bounds_inputs(self):
        for args in (("enumerate", "--n", "-1"), ("enumerate", "--n", "1001"),
                     ("enumerate", "--n", "999999999"), ("coefficients", "--order", "11"),
                     ("coefficients", "--order", "1.0")):
            output = self.root / "bad.json"
            result = self.run_cli(*args, "--output", str(output))
            self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
            self.assertFalse(output.exists())
        source = self.root / "badinput.json"
        source.write_text('{"n": true, "K": 2, "bisections": 8, "exp_terms": 16}')
        result = self.run_cli("certificate", "--input", str(source), "--output", str(self.root / "bad.json"))
        self.assertEqual(result.returncode, 2)
        self.assertFalse((self.root / "bad.json").exists())

    def test_import_has_no_program_side_effects(self):
        code = ("import sys; before=sys.get_int_max_str_digits(); "
                "import fock_exact,safe_io; "
                "raise SystemExit(0 if before==sys.get_int_max_str_digits() else 7)")
        env = dict(os.environ, PYTHONPATH=str(HERE), PYTHONDONTWRITEBYTECODE="1")
        result = subprocess.run([sys.executable, "-B", "-c", code], cwd=self.root,
                                env=env, capture_output=True, text=True, timeout=30)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, "")
        self.assertEqual(result.stderr, "")
        self.assertEqual(list(self.root.iterdir()), [])


if __name__ == "__main__":
    unittest.main()
