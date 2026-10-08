"""Cross-check structural certificates against independent topology computations.

For an integrated tree, place this file in fast/tests and seifert.py in
fast/fastunknot.  Standalone: set PYTHONPATH to baseline/fast and this folder.
"""
from __future__ import annotations

from copy import deepcopy
from pathlib import Path
import json
import random
import unittest

from fastunknot import Diagram, khovanov_rank

try:
    from fastunknot.seifert import seifert_data, seifert_certificate, verify_seifert_certificate
except ImportError:
    from seifert import seifert_data, seifert_certificate, verify_seifert_certificate


class SeifertTests(unittest.TestCase):
    def test_braid_graph_formula_and_relabeling(self):
        rng = random.Random(2026100701)
        checked = 0
        while checked < 160:
            strands = rng.randrange(2, 7)
            word = [rng.choice((-1, 1)) * rng.randrange(1, strands)
                    for _ in range(rng.randrange(strands - 1, 31))]
            try:
                diagram = Diagram.from_braid(strands, word)
            except ValueError:
                continue
            data = seifert_data(diagram)
            self.assertEqual(data["seifert_circles"], strands)
            positive_indices = {g for g in word if g > 0}
            negative_indices = {-g for g in word if g < 0}
            self.assertEqual(data["homogeneity_defect"],
                             len(positive_indices & negative_indices))
            self.assertEqual(data["canonical_genus"], (len(word) - strands + 1) // 2)
            # Half-turn individual PD rows and permute/relabel crossings and edges.
            rows = [row[2:] + row[:2] if rng.randrange(2) else row for row in diagram.pd]
            rng.shuffle(rows)
            labels = list(range(2 * len(word)))
            rng.shuffle(labels)
            moved = Diagram.from_pd([[labels[e] for e in row] for row in rows])
            self.assertEqual(seifert_data(moved), data)
            mirror = seifert_data(diagram.mirror())
            self.assertEqual(mirror["canonical_genus"], data["canonical_genus"])
            self.assertEqual(mirror["homogeneity_defect"], data["homogeneity_defect"])
            lower, upper = data["rasmussen_interval"]
            self.assertEqual(mirror["rasmussen_interval"], [-upper, -lower])
            for candidate in (diagram, moved, diagram.mirror()):
                certificate = seifert_certificate(candidate)
                if certificate is not None:
                    self.assertTrue(verify_seifert_certificate(candidate, certificate))
            checked += 1

    def test_all_three_criteria_and_zero_interval(self):
        cases = [
            (Diagram.from_pd([]), "UNKNOT", "seifert-genus-zero"),
            (Diagram.from_braid(4, [1, -2, 3]), "UNKNOT", "seifert-genus-zero"),
            (Diagram.from_braid(3, [1, -2] * 2), "KNOTTED", "homogeneous-seifert-genus"),
            (Diagram.from_braid(3, [1, 1, 1, 1, -1, 2]), "KNOTTED", "rasmussen-interval"),
        ]
        for diagram, status, criterion in cases:
            certificate = seifert_certificate(diagram)
            self.assertEqual((certificate["status"], certificate["criterion"]), (status, criterion))
            self.assertTrue(verify_seifert_certificate(diagram, certificate))
        figure_eight = seifert_certificate(Diagram.from_braid(3, [1, -2] * 2))
        self.assertEqual(figure_eight["rasmussen_interval"], [0, 0])
        self.assertEqual(figure_eight["status"], "KNOTTED")

    def test_against_exact_khovanov(self):
        rng = random.Random(2026100702)
        checked = fired = 0
        while checked < 60:
            strands = rng.randrange(2, 5)
            word = [rng.choice((-1, 1)) * rng.randrange(1, strands)
                    for _ in range(rng.randrange(strands - 1, 11))]
            try:
                diagram = Diagram.from_braid(strands, word)
            except ValueError:
                continue
            certificate = seifert_certificate(diagram)
            if certificate is not None:
                fired += 1
                rank = khovanov_rank(diagram.pd)["reduced_rank"]
                self.assertEqual(certificate["status"] == "UNKNOT", rank == 1, word)
                self.assertTrue(verify_seifert_certificate(diagram, certificate))
            checked += 1
        self.assertGreater(fired, 20)

    def test_unbounded_genus_unknots_with_defect_one(self):
        for m in (2, 3, 8, 30):
            diagram = Diagram.from_braid(2, [1] * m + [-1] * (m - 1))
            data = seifert_data(diagram)
            self.assertEqual(data["homogeneity_defect"], 1)
            self.assertEqual(data["canonical_genus"], m - 1)
            self.assertIsNone(seifert_certificate(diagram))
            self.assertIsNone(seifert_certificate(diagram.mirror()))

    def test_mutated_certificates_rejected(self):
        diagram = Diagram.from_braid(3, [1, -2] * 4)
        original = seifert_certificate(diagram)
        self.assertTrue(verify_seifert_certificate(diagram, original))
        for key in ("crossings", "writhe", "seifert_circles", "positive_components",
                    "negative_components", "canonical_genus", "homogeneity_defect", "version"):
            changed = deepcopy(original)
            changed[key] += 1
            self.assertFalse(verify_seifert_certificate(diagram, changed), key)
        for key, value in (("status", "UNKNOT"), ("criterion", "seifert-genus-zero"),
                           ("rasmussen_interval", [0, 2]), ("version", True)):
            changed = {**original, key: value}
            self.assertFalse(verify_seifert_certificate(diagram, changed), key)
        self.assertFalse(verify_seifert_certificate(diagram, None))
        self.assertFalse(verify_seifert_certificate(diagram, {}))

    def test_existing_nonhomogeneous_examples_are_inconclusive(self):
        import fastunknot
        examples = Path(fastunknot.__file__).resolve().parent.parent / "examples"
        for name in ("conway.json", "kinoshita_terasaka.json", "hard_unknot_8.json",
                     "grid_scrambled_unknot.json"):
            diagram = Diagram.from_json(json.loads((examples / name).read_text()))
            certificate = seifert_certificate(diagram)
            if name in ("hard_unknot_8.json", "grid_scrambled_unknot.json"):
                self.assertTrue(certificate is None or certificate["status"] == "UNKNOT")
            else:
                self.assertIsNone(certificate)


if __name__ == "__main__":
    unittest.main()

