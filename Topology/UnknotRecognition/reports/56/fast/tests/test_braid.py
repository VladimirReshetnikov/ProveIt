"""Independent checks of the exact source-braid decision backend.

These tests compare two different representations, the old exact Alexander
code, and the independent dense Khovanov cube.  Passing examples or timings is
not used in place of the mathematical proof in the accompanying article.
"""
from __future__ import annotations

import itertools
import json
import os
import pickle
import random
import sys
import unittest
from unittest.mock import patch

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)

from fastunknot import Diagram, DiagramError, braid_certificate, recognize
from fastunknot.alexander import alexander_polynomial, evaluate
from fastunknot.braid import burau_at_minus_one, free_product_normal_form
from test_fastunknot import one_component, reference_reduced_rank


def cyclic_signature(word):
    reduced, _ = free_product_normal_form(word)
    if not reduced:
        return ()
    return min(reduced[i:] + reduced[:i] for i in range(len(reduced)))


class BraidRepresentationTests(unittest.TestCase):
    def test_all_words_through_eight_agree_between_backends(self):
        count = 0
        for length in (2, 4, 6, 8):
            for word in itertools.product((1, -1, 2, -2), repeat=length):
                if not one_component(3, word):
                    continue
                free = braid_certificate(3, word)
                matrix = braid_certificate(3, word, backend="matrix")
                self.assertEqual(free["status"], matrix["status"], word)
                count += 1
        self.assertEqual(count, 46376)

    def test_all_words_through_six_against_independent_khovanov_cube(self):
        count = 0
        for length in (2, 4, 6):
            for word in itertools.product((1, -1, 2, -2), repeat=length):
                if not one_component(3, word):
                    continue
                expected = "UNKNOT" if reference_reduced_rank(Diagram.from_braid(3, word)) == 1 else "KNOTTED"
                self.assertEqual(braid_certificate(3, word)["status"], expected, word)
                count += 1
        self.assertEqual(count, 2856)

    def test_burau_determinant_against_exact_alexander(self):
        rng = random.Random(3270)
        checked = 0
        while checked < 120:
            word = [rng.choice((1, -1, 2, -2)) for _ in range(rng.randrange(1, 10) * 2)]
            if not one_component(3, word):
                continue
            matrix = burau_at_minus_one(word)
            a, b = matrix[0]
            c, d = matrix[1]
            self.assertEqual(a * d - b * c, 1)
            expected = abs(evaluate(alexander_polynomial(Diagram.from_braid(3, word)), -1))
            self.assertEqual(abs(2 - a - d), expected, word)
            checked += 1

    def test_artin_relations_and_conjugation(self):
        rng = random.Random(260107)
        for _ in range(200):
            left = [rng.choice((1, -1, 2, -2)) for _ in range(16)]
            right = [rng.choice((1, -1, 2, -2)) for _ in range(16)]
            for a, b in ((1, 2), (-1, -2)):
                first, second = left + [a, b, a] + right, left + [b, a, b] + right
                self.assertEqual(burau_at_minus_one(first), burau_at_minus_one(second))
                self.assertEqual(cyclic_signature(first), cyclic_signature(second))
            base = left + right
            inverse = [-g for g in reversed(left)]
            self.assertEqual(cyclic_signature(left + base + inverse), cyclic_signature(base))

    def test_long_word_exact_work_bound_and_large_integer_json(self):
        conjugator = [1, -2] * 12001
        word = conjugator + [1, -2] + [-g for g in reversed(conjugator)]
        free = braid_certificate(3, word)
        self.assertEqual(free["status"], "UNKNOT")
        stats = free["free_product_stats"]
        self.assertEqual(stats["token_operations"], 2 * len(word))
        self.assertLessEqual(stats["max_stack_tokens"], 2 * len(word))
        self.assertLessEqual(stats["cyclic_conjugations"], len(word))
        # Large integral witnesses must serialize without converting huge
        # Python integers to decimal strings (the usual 4300-digit ceiling).
        certificate = braid_certificate(3, conjugator, backend="matrix")
        self.assertGreater(certificate["max_entry_bits"], 15000)
        self.assertEqual(certificate["status"], "KNOTTED")
        self.assertEqual(json.loads(json.dumps(certificate)), certificate)


class BraidPipelineTests(unittest.TestCase):
    def test_invalid_and_unsupported_inputs(self):
        for strands, word in ((0, []), (True, []), (3, [1]), (2, [1, 1]),
                              (3, [1, 3]), (3, [1, 2.0]), (1, [1]), (3, None)):
            with self.assertRaises(DiagramError):
                braid_certificate(strands, word)
        with self.assertRaises(ValueError):
            braid_certificate(3, [1, 2], backend="guess")

    def test_elementary_cases_and_necessary_writhe_bound(self):
        self.assertEqual(braid_certificate(1, [])["status"], "UNKNOT")
        for exponent in (1, -1, 3, -3, 31, -31):
            result = braid_certificate(2, [1 if exponent > 0 else -1] * abs(exponent))
            self.assertEqual(result["status"], "UNKNOT" if abs(exponent) == 1 else "KNOTTED")
        # Determinant alone cannot decide, even on three strands: T(3,5).
        word = [1, 2] * 5
        matrix = burau_at_minus_one(word)
        self.assertEqual(abs(2 - matrix[0][0] - matrix[1][1]), 1)
        self.assertEqual(braid_certificate(3, word)["method"], "braid-bennequin")
        self.assertEqual(braid_certificate(3, word)["status"], "KNOTTED")
        self.assertEqual(braid_certificate(4, [1, 2, 3] * 3)["method"], "braid-bennequin")

    def test_provenance_is_checked_immutable_and_serializable(self):
        word = [1, -2, 1, -2]
        diagram = Diagram.from_json({"braid": {"strands": 3, "word": word}})
        expected = diagram.braid_source
        word.append(1)
        self.assertEqual(diagram.braid_source, expected)
        with self.assertRaises(AttributeError):
            diagram.braid_source = (3, (1, 2))
        with self.assertRaises(TypeError):
            Diagram(diagram.pd, braid_source=(3, (1, 2)))
        pd_only = Diagram.from_pd(diagram.pd)
        self.assertIsNone(pd_only.braid_source)
        self.assertEqual(pd_only, diagram)
        self.assertEqual(hash(pd_only), hash(diagram))
        for value in (diagram, diagram.mirror(), pd_only):
            restored = pickle.loads(pickle.dumps(value))
            self.assertEqual(restored, value)
            self.assertEqual(restored.braid_source, value.braid_source)
        retained = Diagram.from_json(diagram.to_json(preserve_braid=True))
        self.assertEqual(retained.braid_source, diagram.braid_source)
        self.assertIsNone(Diagram.from_json(diagram.to_json()).braid_source)
        corrupted = diagram.__getstate__()
        corrupted["braid_source"] = (3, (1, 2, 1, 2))
        with self.assertRaises(DiagramError):
            object.__new__(Diagram).__setstate__(corrupted)
        with self.assertRaises(AttributeError):
            diagram.__setstate__(pd_only.__getstate__())

    def test_early_dispatch_opt_out_and_resource_limit(self):
        word = [1, -2] * 7
        diagram = Diagram.from_braid(3, word)
        with patch("fastunknot.recognize.khovanov_rank", side_effect=AssertionError("scan called")):
            with patch("fastunknot.recognize.simplify", side_effect=AssertionError("reducer called")):
                result = recognize(diagram)
        self.assertEqual((result.status, result.method), ("KNOTTED", "three-braid-free-product"))
        self.assertEqual(recognize(diagram, braid_backend="matrix").method, "three-braid-matrix")
        self.assertEqual(recognize(diagram, use_braid=False).status, result.status)
        self.assertFalse(result.to_json()["quasipolynomial_guarantee"])
        self.assertEqual(recognize(diagram, seconds=0).status, "UNKNOWN")

    def test_mirrors_and_real_four_strand_fallback(self):
        for word in ([1, 2], [1, -2], [1, -2] * 2, [1, 2] * 5):
            original = Diagram.from_braid(3, word)
            self.assertEqual(recognize(original).status, recognize(original.mirror()).status)
        # Morton's irreducible four-braid representative of the unknot.
        # Neither endpoint occurs once, so the exact PD fallback is required.
        morton = [-3, -3, 2, -3, 2, 1, 1, 1, -2, 1, -2]
        self.assertEqual(braid_certificate(4, morton)["status"], "INCONCLUSIVE")
        self.assertEqual(recognize(Diagram.from_braid(4, morton)).status, "UNKNOT")

    def test_diagram_reductions_precede_endpoint_descent(self):
        chain = Diagram.from_braid(257, range(1, 257))
        with patch("fastunknot.braid_reduction.singleton_reduce", side_effect=AssertionError("descent called")):
            result = recognize(chain, use_seifert=False)
        self.assertEqual((result.status, result.method), ("UNKNOT", "reidemeister-reduction"))
        stabilized_figure_eight = Diagram.from_braid(4, [1, -2, 1, -2, 3])
        result = recognize(stabilized_figure_eight, use_seifert=False)
        self.assertEqual((result.status, result.method),
                         ("KNOTTED", "braid-destabilization:three-braid-free-product"))
        self.assertEqual((result.input_crossings, result.reduced_crossings), (5, 4))
        self.assertEqual(result.evidence["braid"]["strands"], 4)
        self.assertEqual(result.evidence["braid"]["after_reduction"]["strands"], 3)
        self.assertEqual(recognize(stabilized_figure_eight, use_seifert=False, use_braid_reduction=False).method,
                         "alexander-modular")


if __name__ == "__main__":
    unittest.main()
