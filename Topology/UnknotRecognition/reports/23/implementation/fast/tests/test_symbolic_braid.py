"""Independent expanded-diagram and exact-homology checks of run certificates."""
from copy import deepcopy
import json
from pathlib import Path
import random
import subprocess
import sys
import unittest

from fastunknot import Diagram, khovanov_rank
from fastunknot.seifert import seifert_certificate, seifert_data
from fastunknot.symbolic_braid import (
    encoded_integer, json_safe, load_braid, recognize_runs,
    signed_run_certificate, signed_run_seifert_data,
    verify_signed_run_certificate,
)
from fastunknot.twist.core import Budget, Run, components, runs_from_word


class SymbolicBraidTests(unittest.TestCase):
    def test_signed_graph_counts_against_expanded_pd(self):
        rng = random.Random(2026100817)
        checked = 0
        while checked < 180:
            strands = rng.randrange(2, 7)
            word = [rng.choice((-1, 1)) * rng.randrange(1, strands)
                    for _ in range(rng.randrange(strands - 1, 26))]
            runs = runs_from_word(strands, word)
            if components(strands, runs) != 1:
                continue
            diagram = Diagram.from_braid(strands, word)
            self.assertEqual(signed_run_seifert_data(strands, runs), seifert_data(diagram))
            observed = signed_run_certificate(strands, runs)
            expanded = seifert_certificate(diagram)
            if expanded is None:
                self.assertIsNone(observed)
            else:
                self.assertEqual((observed["status"], observed["criterion"]),
                                 (expanded["status"], expanded["criterion"]))
                self.assertTrue(verify_signed_run_certificate(strands, runs, observed))
            checked += 1

    def test_structural_verdicts_against_exact_khovanov(self):
        rng = random.Random(2026100818)
        checked = fired = 0
        while checked < 40:
            strands = rng.randrange(2, 5)
            word = [rng.choice((-1, 1)) * rng.randrange(1, strands)
                    for _ in range(rng.randrange(strands - 1, 10))]
            runs = runs_from_word(strands, word)
            if components(strands, runs) != 1:
                continue
            cert = signed_run_certificate(strands, runs)
            if cert is not None:
                exact = khovanov_rank(Diagram.from_braid(strands, word).pd)
                self.assertEqual(cert["status"] == "UNKNOT", exact["reduced_rank"] == 1)
                fired += 1
            checked += 1
        self.assertGreater(fired, 0)

    def test_empty_and_all_structural_criteria(self):
        cases = [(1, [], "UNKNOT", "seifert-genus-zero"),
                 (4, [1, -2, 3], "UNKNOT", "seifert-genus-zero"),
                 (3, [1, -2] * 2, "KNOTTED", "homogeneous-seifert-genus"),
                 (3, [1, 1, 1, 1, -1, 2], "KNOTTED", "rasmussen-interval")]
        for strands, word, status, criterion in cases:
            runs = runs_from_word(strands, word)
            cert = signed_run_certificate(strands, runs)
            self.assertEqual((cert["status"], cert["criterion"]), (status, criterion))
            self.assertTrue(verify_signed_run_certificate(strands, runs, cert))

    def test_twenty_thousand_bit_balanced_runs_never_expand(self):
        exponent = (1 << 20000) + 1
        # Each generator has only one sign, but no selected run dominates its context.
        runs = (Run(1, exponent), Run(2, -exponent), Run(3, exponent))
        result = recognize_runs(4, runs, budget=Budget(max_states=0, max_basis=0))
        self.assertEqual(result["status"], "KNOTTED")
        self.assertEqual(result["method"], "signed-run-structural")
        self.assertEqual(result["certificate"]["crossings"], 3 * exponent)
        self.assertTrue(verify_signed_run_certificate(4, runs, result["certificate"]))
        encoded = json.dumps(json_safe(result))
        decoded = json.loads(encoded)
        self.assertEqual(encoded_integer(decoded["certificate"]["crossings"]), 3 * exponent)

    def test_inconclusive_unknot_uses_exact_fallback(self):
        runs = (Run(1, 5), Run(1, -4))
        self.assertIsNone(signed_run_certificate(2, runs))
        result = recognize_runs(2, runs, check_d2=True)
        self.assertEqual(result["status"], "UNKNOT")
        self.assertEqual(result["method"], "symbolic-twist-khovanov-F2")
        self.assertEqual(result["homology"]["reduced_rank"], 1)

    def test_resource_limits_are_unknown(self):
        runs = (Run(1, 5), Run(1, -4))
        for budget in (Budget(max_basis=0), Budget(seconds=0), Budget(max_xors=0)):
            result = recognize_runs(2, runs, budget=budget, check_d2=True)
            self.assertEqual(result["status"], "UNKNOWN")
        self.assertEqual(recognize_runs(2, (Run(1, 3),), budget=Budget(seconds=0))["status"],
                         "UNKNOWN")

    def test_invalid_inputs_and_options_are_not_early_verdicts(self):
        for strands, runs in ((0, ()), (True, ()), (2, (Run(1, 0),)),
                              (2, (Run(2, 1),)), (2, (Run(1, True),)),
                              (2, (Run(1, 2),)), (10**100, ())):
            with self.assertRaises(ValueError):
                recognize_runs(strands, runs)
        for selected in (-1, 1, True, "0"):
            with self.assertRaises(ValueError):
                recognize_runs(2, (Run(1, 3),), selected=selected)
        cap = Budget()
        cap.max_basis = -1
        with self.assertRaises(ValueError):
            recognize_runs(2, (Run(1, 3),), budget=cap)

    def test_tampered_certificates_fail_independent_replay(self):
        runs = (Run(1, 11), Run(2, -7), Run(3, 9))
        original = signed_run_certificate(4, runs)
        self.assertTrue(verify_signed_run_certificate(4, runs, original))
        for key, value in original.items():
            changed = deepcopy(original)
            if type(value) is int:
                changed[key] += 1
            elif isinstance(value, list):
                changed[key][0] += 1
            else:
                changed[key] += " corrupt"
            self.assertFalse(verify_signed_run_certificate(4, runs, changed), key)
        for key in ("version", "crossings", "canonical_genus"):
            self.assertFalse(verify_signed_run_certificate(4, runs, {**original, key: True}))
        self.assertFalse(verify_signed_run_certificate(4, runs, {**original, "extra": 0}))
        self.assertFalse(verify_signed_run_certificate(4, runs, None))
        self.assertFalse(verify_signed_run_certificate(10**100, (), original))

    def test_complete_huge_certificate_json_round_trip(self):
        magnitude = (1 << 20000) + 1
        for sign in (-1, 1):
            runs = (Run(1, sign * magnitude),)
            original = signed_run_certificate(2, runs)
            transported = json.loads(json.dumps(json_safe(original)))
            self.assertIsInstance(transported["rasmussen_interval"][0], str)
            self.assertTrue(verify_signed_run_certificate(2, runs, transported))
            for key, value in (("crossings", "0x0"), ("crossings", True),
                               ("writhe", "0x"), ("canonical_genus", "123"),
                               ("version", "0x1"), ("rasmussen_interval", ["0x0", "0x0"])):
                self.assertFalse(verify_signed_run_certificate(2, runs, {**transported, key: value}))
            self.assertFalse(verify_signed_run_certificate(2, runs, {**transported, "extra": "0x1"}))

    def test_json_validation_and_arbitrary_size_hex(self):
        exponent = (1 << 20000) + 1
        strands, runs = load_braid({"braid": {"strands": 2, "runs": [[1, hex(exponent)]]}})
        self.assertEqual((strands, runs), (2, (Run(1, exponent),)))
        self.assertEqual(load_braid({"strands": "0x2", "word": [1, "-0x1", 1]})[1],
                         (Run(1, 1), Run(1, -1), Run(1, 1)))
        for value in (None, [], {}, {"strands": 2}, {"strands": 2, "runs": [[1]]},
                      {"strands": 2, "runs": [[1, "123"]]},
                      {"strands": True, "runs": []},
                      {"strands": 2, "runs": [], "word": []}):
            with self.assertRaises((ValueError, TypeError)):
                load_braid(value)
        for value in (True, 1.5, "1", "0x", "__import__('os')"):
            with self.assertRaises(ValueError):
                encoded_integer(value)

    def test_cli_modes_exit_codes_and_hex_output(self):
        def invoke(data, *arguments):
            process = subprocess.run([sys.executable, "-m", "fastunknot.symbolic_braid", "-",
                                      *arguments], input=json.dumps(data), text=True,
                                     capture_output=True, check=False, timeout=20)
            return process.returncode, json.loads(process.stdout)
        huge = (1 << 20000) + 1
        data = {"strands": 2, "runs": [[1, hex(huge)]]}
        code, result = invoke(data)
        self.assertEqual((code, result["status"]), (0, "KNOTTED"))
        self.assertEqual(encoded_integer(result["certificate"]["crossings"]), huge)
        code, result = invoke(data, "--mode", "homology", "--check-d2")
        self.assertEqual(code, 0)
        self.assertEqual(encoded_integer(result["reduced_rank"]), huge)
        code, result = invoke(data, "--mode", "certificate", "--seconds", "0")
        self.assertEqual((code, result["status"]), (3, "UNKNOWN"))
        code, result = invoke(data, "--selected-run", "1")
        self.assertEqual((code, result["status"]), (2, "INVALID"))
        code, result = invoke({"strands": 2, "runs": [[1, 5], [1, -4]]}, "--mode", "certificate")
        self.assertEqual((code, result["status"]), (3, "INCONCLUSIVE"))


if __name__ == "__main__":
    unittest.main()
