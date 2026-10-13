import copy
import json
import unittest
from itertools import product
from pathlib import Path

from fastunknot.diagram import Diagram, DiagramError
from fastunknot.tangle_obstruction import (
    PatternError, _compile, _template_topology, find_subtangle_obstruction,
    recognize_with_subtangles, verify_subtangle_certificate,
)

EXAMPLES = Path(__file__).resolve().parents[1] / "examples"
CERTIFICATES = Path(__file__).resolve().parents[1] / "certificates"


class SubtangleTests(unittest.TestCase):
    def setUp(self):
        self.pattern = {"e": 0, "tangles": [[0, -3], [0, 5], [0, 7]]}
        self.diagram = Diagram.from_json(json.loads(
            (EXAMPLES / "conway_forbidden_pretzel.json").read_text()))
        self.certificate = json.loads(
            (CERTIFICATES / "conway_forbidden_pretzel_certificate.json").read_text())

    def test_local_certificate_and_automatic_discovery(self):
        evidence = verify_subtangle_certificate(self.diagram, self.certificate)
        self.assertEqual(evidence["status"], "KNOTTED")
        self.assertEqual(evidence["pattern_crossings"], 15)
        cert, evidence, stats = find_subtangle_obstruction(self.diagram, [self.pattern])
        self.assertIsNotNone(cert)
        self.assertEqual(evidence["status"], "KNOTTED")
        self.assertLessEqual(stats["root_trials"], 2 * self.diagram.crossings)
        self.assertLessEqual(stats["crossings_visited"],
                             2 * self.diagram.crossings * 15)

    def test_reordered_crossings_and_even_rotations(self):
        rows = list(reversed(self.diagram.pd))
        rows = [row[2:] + row[:2] if i % 2 else row for i, row in enumerate(rows)]
        changed = Diagram.from_pd(rows)
        cert, evidence, _ = find_subtangle_obstruction(changed, [self.pattern])
        self.assertIsNotNone(cert)
        self.assertEqual(verify_subtangle_certificate(changed, cert), evidence)

    def test_tampering_rejected(self):
        cases = []
        bad = copy.deepcopy(self.certificate); bad["crossings"][1] = bad["crossings"][0]; cases.append(bad)
        bad = copy.deepcopy(self.certificate); bad["rotations"][0] = 1; cases.append(bad)
        bad = copy.deepcopy(self.certificate); bad["crossings"][0] = -1; cases.append(bad)
        bad = copy.deepcopy(self.certificate); bad["pattern"]["tangles"][0] = [0, 3]; cases.append(bad)
        bad = copy.deepcopy(self.certificate); bad["version"] = True; cases.append(bad)
        bad = copy.deepcopy(self.certificate); bad["status"] = "KNOTTED"; cases.append(bad)
        bad = copy.deepcopy(self.certificate); bad["pattern"]["tangles"][0] = [0, 10**100]; cases.append(bad)
        for certificate in cases:
            with self.subTest(certificate=str(certificate)[:60]):
                with self.assertRaises((PatternError, DiagramError)):
                    verify_subtangle_certificate(self.diagram, certificate)
        trefoil = Diagram.from_braid(2, [1, 1, 1])
        with self.assertRaises(PatternError):
            verify_subtangle_certificate(trefoil, self.certificate)

    def test_ports_and_closed_strings(self):
        source = (0, ((0, 3), (0, 3)))
        template, _, arithmetic = _compile(source)
        self.assertEqual(arithmetic["residue"], 6)
        bad_boundary = list(template["boundary"])
        bad_boundary[0], bad_boundary[1] = bad_boundary[1], bad_boundary[0]
        with self.assertRaises(PatternError):
            _template_topology(template["pd"], tuple(bad_boundary))
        with self.assertRaises(PatternError):
            _compile((0, ((0, 2), (0, 2))))
        with self.assertRaises(PatternError):
            _compile((0, ((0, 2), (0, 3))))

    def test_default_catalogue_and_fallback(self):
        diagram = Diagram.from_json(json.loads(
            (EXAMPLES / "conway_double_three.json").read_text()))
        cert, evidence, _ = find_subtangle_obstruction(diagram)
        self.assertIsNotNone(cert)
        self.assertEqual(evidence["arithmetic"]["criterion"],
                         "two-summand-congruence-obstruction")
        result = recognize_with_subtangles(diagram)
        self.assertEqual((result.status, result.method), ("KNOTTED", "montesinos-subtangle"))
        result = recognize_with_subtangles(Diagram.from_pd([]))
        self.assertEqual(result.status, "UNKNOT")
        result = recognize_with_subtangles(diagram, seconds=0)
        self.assertEqual(result.status, "UNKNOWN")

    def test_no_false_rejection_on_short_closed_braids(self):
        from fastunknot.recognize import recognize
        checked, hits = 0, 0
        for length in (2, 4, 6):
            for word in product((1, -1, 2, -2), repeat=length):
                if length == 6 and word[0:2] not in ((1, 2), (-1, -2)):
                    continue
                try:
                    diagram = Diagram.from_braid(3, word)
                except DiagramError:
                    continue
                cert, _, _ = find_subtangle_obstruction(diagram)
                checked += 1
                if cert is not None:
                    hits += 1
                    self.assertEqual(recognize(diagram).status, "KNOTTED")
        self.assertGreater(checked, 100)


if __name__ == "__main__":
    unittest.main()
