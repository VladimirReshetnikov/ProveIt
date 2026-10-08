"""Independent checks of exact Montesinos arithmetic, PDs and provenance."""
from __future__ import annotations

import copy
import itertools
import json
import os
import pickle
import random
import sys
import unittest
from collections import Counter
from unittest.mock import patch

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)

from fastunknot import (Diagram, DiagramError, continued_fraction,
                       montesinos_certificate, recognize, verify_montesinos_certificate)
from fastunknot.alexander import alexander_polynomial, evaluate
from fastunknot.rational import build_montesinos_tangle
from fastunknot.simplify import simplify
from test_fastunknot import reference_reduced_rank


def euclidean_cf(p, q):
    result = []
    while q:
        quotient, remainder = divmod(p, q)
        result.append(quotient)
        p, q = q, remainder
    return result


def binary_slope(word, p, q):
    for letter in reversed(word):
        if letter == "A":
            p += 2 * q
        else:
            q += 2 * p
    return p, q


def identity_source(left, right):
    p, q = binary_slope(left, 1, 1)
    r, s = binary_slope(right, 3, 2)
    return [euclidean_cf(p, q), [-a for a in euclidean_cf(r, s)]]


class RationalArithmeticTests(unittest.TestCase):
    def test_projective_cf_zero_denominators_and_mirrors(self):
        cases = { (3,): (3, 1), (1, 2): (3, 2), (0, 3): (1, 3),
                  (1, 0, 2): (3, 1), (0, 0): (1, 0),
                  (1, 0, 0): (1, 1), (-2, 3): (-5, 3) }
        for cf, expected in cases.items():
            self.assertEqual(continued_fraction(cf), expected)
            p, q = expected
            mirrored = continued_fraction([-a for a in cf])
            self.assertEqual(mirrored, (-p, q) if q else (1, 0))
        with self.assertRaises(DiagramError):
            montesinos_certificate(0, [[0, 0]])

    def test_integer_normalization_preserves_the_full_product(self):
        first = montesinos_certificate(0, [[2, 2], [-2, 3], [4]])
        second = montesinos_certificate(4, [[0, 2], [0, 3]])
        self.assertEqual(first["normalized_e"], second["normalized_e"])
        self.assertEqual(first["exceptional_fibres"], second["exceptional_fibres"])
        self.assertEqual(first["determinant"], second["determinant"])
        # 1/2+1/2 reduces as a number to 1, but its closure determinant is 4.
        # It is a link and must never acquire a rank-one/unknot verdict.
        with self.assertRaises(DiagramError):
            montesinos_certificate(0, [[0, 2], [0, 2]])
        with self.assertRaises(DiagramError):
            Diagram.from_rational(0, [[0, 2], [0, 2]])

    def test_three_exceptional_fibres_detect_determinant_one_knots(self):
        for alpha in (5, 7):
            source = [[0, 2], [0, 3], [0, alpha]]
            certificate = montesinos_certificate(-1, source)
            self.assertEqual(certificate["determinant"], 1)
            self.assertEqual(certificate["exceptional_count"], 3)
            self.assertEqual(certificate["status"], "KNOTTED")
            self.assertEqual(certificate["method"], "montesinos-orbifold-quotient")
            diagram = Diagram.from_rational(-1, source)
            self.assertEqual(abs(evaluate(alexander_polynomial(diagram), -1)), 1)
            self.assertEqual(recognize(diagram, use_rational=False).status, "KNOTTED")

    def test_binary_coefficient_arithmetic_does_not_expand(self):
        huge = (1 << 20000) + 1
        certificate = montesinos_certificate(0, [[0, huge]])
        self.assertEqual(certificate["status"], "UNKNOT")
        self.assertIsInstance(certificate["expanded_crossings"], dict)
        self.assertEqual(json.loads(json.dumps(certificate)), certificate)
        self.assertTrue(verify_montesinos_certificate(0, [[0, huge]], certificate))
        with self.assertRaises(DiagramError):
            Diagram.from_rational(0, [[0, huge]])
        with self.assertRaises(DiagramError):
            Diagram.from_rational(0, [[0, 11]], max_crossings=10)
        self.assertEqual(Diagram.from_rational(0, [[0, 11]], max_crossings=11).crossings, 11)
        for cap in (-1, True, 2.5):
            with self.assertRaises(ValueError):
                Diagram.from_rational(0, [[1]], max_crossings=cap)

    def test_certificate_replay_and_tampering(self):
        source = (-1, [[0, 2], [0, 3], [0, 5]])
        certificate = montesinos_certificate(*source)
        self.assertTrue(verify_montesinos_certificate(*source, certificate))
        for key, replacement in (("status", "UNKNOT"), ("determinant", 3),
                                 ("version", True), ("exceptional_count", 2),
                                 ("normalized_e", 0), ("max_entry_bits", 1)):
            changed = dict(certificate)
            changed[key] = replacement
            self.assertFalse(verify_montesinos_certificate(*source, changed), key)
        changed = copy.deepcopy(certificate)
        changed["primitive_slopes"][0][1] = 3
        self.assertFalse(verify_montesinos_certificate(*source, changed))
        changed = dict(certificate, extra="not a verified field")
        self.assertFalse(verify_montesinos_certificate(*source, changed))

    def test_invalid_source_inputs(self):
        for e, tangles in ((True, [[1]]), (0, [[]]), (0, [[True]]), (0, [[1.0]]),
                           (0, ["123"]), (0, [{1: 2}]), (0, "123"), (0, None)):
            with self.assertRaises(DiagramError):
                montesinos_certificate(e, tangles)
        for value in ({"pd": [], "montesinos": {"tangles": [[1]]}},
                      {"montesinos": {"tangles": [[1]], "fraction": [1, 1]}},
                      {"montesinos": {"e": 1}}, {"montesinos": []}):
            with self.assertRaises(DiagramError):
                Diagram.from_json(value)
        with self.assertRaises(DiagramError):
            montesinos_certificate(0, [])
        self.assertEqual(montesinos_certificate(1, [])["status"], "UNKNOT")


class RationalDiagramTests(unittest.TestCase):
    def test_small_cf_corpus_against_independent_khovanov_cube(self):
        count = 0
        for length in (1, 2, 3):
            for cf in itertools.product((-2, -1, 0, 1, 2), repeat=length):
                p, q = continued_fraction(cf)
                if not q or not p % 2 or sum(abs(a) for a in cf) > 5:
                    continue
                diagram = Diagram.from_rational(0, [cf])
                expected = "UNKNOT" if reference_reduced_rank(diagram) == 1 else "KNOTTED"
                certificate = montesinos_certificate(0, [cf])
                self.assertEqual(certificate["status"], expected, cf)
                self.assertTrue(verify_montesinos_certificate(0, [cf], certificate))
                count += 1
        self.assertGreater(count, 50)

    def test_random_montesinos_determinants_against_exact_alexander(self):
        rng = random.Random(20261008)
        count = 0
        while count < 160:
            e = rng.randrange(-2, 3)
            tangles = [[rng.randrange(-2, 3) for _ in range(rng.randrange(1, 4))]
                       for _ in range(rng.randrange(1, 5))]
            try:
                certificate = montesinos_certificate(e, tangles)
            except DiagramError:
                continue
            diagram = Diagram.from_rational(e, tangles)
            self.assertEqual(diagram.crossings, abs(e) + sum(abs(a) for cf in tangles for a in cf))
            self.assertEqual(abs(evaluate(alexander_polynomial(diagram), -1)),
                             certificate["determinant"], (e, tangles))
            self.assertTrue(verify_montesinos_certificate(e, tangles, certificate))
            count += 1

    def test_small_two_tangle_corpus_against_independent_cube(self):
        choices = ([0, 2], [0, -2], [0, 3], [0, -3], [1, 2], [-1, -2])
        count = 0
        for e in (-1, 0, 1):
            for left, right in itertools.product(choices, repeat=2):
                try:
                    certificate = montesinos_certificate(e, [left, right])
                except DiagramError:
                    continue
                diagram = Diagram.from_rational(e, [left, right])
                rank = reference_reduced_rank(diagram)
                self.assertEqual(certificate["status"], "UNKNOT" if rank == 1 else "KNOTTED",
                                 (e, left, right))
                count += 1
        self.assertGreater(count, 30)

    def test_four_terminal_graph_contract(self):
        for source in ((0, [[0, 2], [0, 3]]), (-1, [[0, 2], [0, 3], [0, 5]]),
                       (0, [[1, 0, 0]]), (0, [[0, 2], [0, 2]])):
            tangle = build_montesinos_tangle(*source)
            occurrences = Counter(tangle["boundary"])
            occurrences.update(label for row in tangle["pd"] for label in row)
            self.assertTrue(all(count == 2 for count in occurrences.values()), source)
            self.assertEqual(tangle["boundary_order"], "NW,NE,SE,SW")
            self.assertEqual(len(tangle["boundary"]), 4)

    def test_checked_provenance_serialization_and_mirror(self):
        cf = [[3, 2], [-3, -3]]
        diagram = Diagram.from_rational(0, cf)
        source = diagram.rational_source
        cf[0].append(2)
        self.assertEqual(diagram.rational_source, source)
        with self.assertRaises(AttributeError):
            diagram.rational_source = (0, ((1,),))
        with self.assertRaises(TypeError):
            Diagram(diagram.pd, rational_source=(0, ((1,),)))
        # Reinvoking __init__ must not replace a certified unknot's PD while
        # leaving its old source record attached.
        trefoil = Diagram.from_braid(2, [1, 1, 1])
        with self.assertRaises(AttributeError):
            diagram.__init__(trefoil.pd)
        self.assertEqual(recognize(diagram).status, "UNKNOT")
        bare = Diagram.from_pd(diagram.pd)
        self.assertEqual(bare, diagram)
        self.assertEqual(hash(bare), hash(diagram))
        self.assertIsNone(bare.rational_source)
        for candidate in (diagram, diagram.mirror(), bare):
            restored = pickle.loads(pickle.dumps(candidate))
            self.assertEqual(restored, candidate)
            self.assertEqual(restored.rational_source, candidate.rational_source)
        saved = Diagram.from_json(diagram.to_json(preserve_rational=True))
        self.assertEqual(saved.rational_source, source)
        self.assertIsNone(Diagram.from_json(diagram.to_json()).rational_source)
        corrupted = diagram.__getstate__()
        corrupted["rational_source"] = (0, ((1,),))
        with self.assertRaises(DiagramError):
            object.__new__(Diagram).__setstate__(corrupted)
        corrupted = diagram.__getstate__()
        corrupted["braid_source"] = (2, (1,))
        with self.assertRaises(DiagramError):
            object.__new__(Diagram).__setstate__(corrupted)
        with self.assertRaises(AttributeError):
            diagram.__setstate__(bare.__getstate__())

    def test_identity_continuation_matrix_and_cancellation_hard_unknot(self):
        words = list(itertools.product("AB", repeat=3))
        for left, right in itertools.product(words, repeat=2):
            tangles = identity_source(left, right)
            certificate = montesinos_certificate(0, tangles)
            self.assertEqual(certificate["status"], "UNKNOT" if left == right else "KNOTTED")
            diagram = Diagram.from_rational(0, tangles)
            self.assertEqual(diagram.crossings, 16)
            self.assertEqual(abs(evaluate(alexander_polynomial(diagram), -1)),
                             certificate["determinant"])
        hard = Diagram.from_rational(0, identity_source("AB", "AB"))
        # At least one two-letter identity word is irreducible by current RI/RII.
        hard_candidates = [Diagram.from_rational(0, identity_source(w, w))
                           for w in itertools.product("AB", repeat=2)]
        hard = next(d for d in hard_candidates if simplify(d, r3=False)[0].crossings == d.crossings)
        self.assertEqual(hard.crossings, 12)
        self.assertEqual(recognize(hard, use_rational=False).method, "reduced-khovanov-F2-scan")
        with patch("fastunknot.recognize.khovanov_rank", side_effect=AssertionError("scan called")):
            with patch("fastunknot.recognize.simplify", side_effect=AssertionError("reducer called")):
                result = recognize(hard)
        self.assertEqual((result.status, result.method), ("UNKNOT", "montesinos-two-bridge-determinant"))
        self.assertEqual(recognize(hard, seconds=0).status, "UNKNOWN")
        self.assertFalse(result.to_json()["quasipolynomial_guarantee"])


if __name__ == "__main__":
    unittest.main()
