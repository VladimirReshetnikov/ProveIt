"""Meaningful differential, invariance, adversarial-certificate, and limit tests."""
from __future__ import annotations

import copy
import itertools
import json
import random
import unittest
from pathlib import Path

import fastunknot
from fastunknot import Diagram, khovanov_rank

from fastunknot.finite_quotient import (find_a5_by_seeds, find_a5_certificate, wirtinger_data,
                             wirtinger_seed_plan, a5_seed_orbit_count, _palette,
                             _seed_assignments)
from fastunknot.finite_quotient_check import verify_certificate


EXAMPLES = Path(fastunknot.__file__).resolve().parent.parent / "examples"


def load(name):
    return Diagram.from_json(json.loads((EXAMPLES / (name + ".json")).read_text()))


def reference_arcs(diagram):
    """Construct oriented arcs by walking from underpass to underpass.

    This deliberately avoids union-find and Diagram's traversal/sign methods.
    """
    pd = diagram.pd
    occurrences = {}
    for i, row in enumerate(pd):
        for j, edge in enumerate(row):
            occurrences.setdefault(edge, []).append((i, j))
    edge_arc = {}
    incoming = {}
    current, arc = (0, 0), -1
    for _ in range(2 * len(pd)):
        i, j = current
        incoming[i, j % 2] = j
        if j % 2 == 0:
            arc += 1
        outgoing = (i, (j + 2) % 4)
        edge = pd[i][outgoing[1]]
        edge_arc[edge] = arc
        left, right = occurrences[edge]
        current = right if left == outgoing else left
    assert arc == len(pd) - 1 and current == (0, 0)
    relations = []
    for i, row in enumerate(pd):
        u, o = incoming[i, 0], incoming[i, 1]
        sign = 1 if (o - u) % 4 == 3 else -1
        relations.append((edge_arc[row[1]], edge_arc[row[u]], edge_arc[row[(u + 2) % 4]], sign))
    return [edge_arc[e] for e in range(2 * len(pd))], relations


def reference_exists(diagram, order):
    """Full assignment enumeration with direct permutations and independent arcs."""
    _, relations = reference_arcs(diagram)
    seeds = {2: (1, 0, 3, 2, 4), 3: (1, 2, 0, 3, 4), 5: (1, 2, 3, 4, 0)}

    def mul(a, b):
        return tuple(a[b[x]] for x in range(5))

    def inv(a):
        return tuple(a.index(x) for x in range(5))

    def conj(a, b):
        return mul(mul(a, b), inv(a))

    group = [p for p in itertools.permutations(range(5))
             if sum(p[i] > p[j] for i in range(5) for j in range(i + 1, 5)) % 2 == 0]
    colors = sorted({conj(g, seeds[order]) for g in group})
    for rest in itertools.product(colors, repeat=len(relations) - 1):
        images = (colors[0],) + rest
        if all(image == images[0] for image in images):
            continue
        if all(conj(images[o] if s == 1 else inv(images[o]), images[u]) == images[v]
               for o, u, v, s in relations):
            return True
    return False


class FiniteQuotientTests(unittest.TestCase):
    def test_burnside_orbit_counts(self):
        for order, q in ((2, 15), (3, 20), (5, 12)):
            colors, _, stabilizer = _palette(order)
            self.assertEqual(len(colors), q)
            for b in (1, 2, 3, 4):
                count = sum(1 for _ in _seed_assignments(q, b - 1, stabilizer))
                self.assertEqual(count, a5_seed_orbit_count(order, b))
        self.assertEqual([a5_seed_orbit_count(order, 3) for order in (2, 3, 5)], [63, 136, 32])

    def test_named_determinant_one_witnesses(self):
        for name in ("conway", "kinoshita_terasaka", "torus_3_5", "grid_determinant_one_knot"):
            diagram = load(name)
            for solve in (find_a5_certificate, find_a5_by_seeds):
                result = solve(diagram, classes=(3,))
                self.assertEqual(result["status"], "KNOTTED", (name, solve.__name__))
                self.assertTrue(verify_certificate(diagram.pd, result["certificate"])["valid"])

    def test_seed_plans_replay(self):
        for name in ("conway", "kinoshita_terasaka", "hard_unknot_8", "stress_braid5_36",
                     "conway_sum_8"):
            diagram = load(name)
            plan = wirtinger_seed_plan(diagram)
            owner, relations = wirtinger_data(diagram)
            self.assertEqual(owner, plan["edge_arcs"])
            known = set(plan["seed_arcs"])
            for step in plan["steps"]:
                o, u, v, _ = relations[step["crossing"]]
                target = step["target_arc"]
                self.assertIn(o, known)
                self.assertNotIn(target, known)
                self.assertTrue(target == u and v in known or target == v and u in known)
                known.add(target)
            self.assertEqual(known, set(range(diagram.crossings)))
        self.assertEqual(len(wirtinger_seed_plan(load("conway"))["seed_arcs"]), 3)
        self.assertEqual(len(wirtinger_seed_plan(load("kinoshita_terasaka"))["seed_arcs"]), 3)

    def test_independent_arc_extraction(self):
        rng = random.Random(2201)
        for name in ("trefoil", "figure_eight", "conway", "kinoshita_terasaka", "hard_unknot_8"):
            diagram = load(name)
            for _ in range(8):
                rows = [row[2:] + row[:2] if rng.randrange(2) else row for row in diagram.pd]
                rng.shuffle(rows)
                transformed = Diagram.from_pd(rows)
                actual, _ = wirtinger_data(transformed)
                reference, _ = reference_arcs(transformed)
                pairs = dict(zip(actual, reference))
                self.assertEqual(len(set(pairs.values())), transformed.crossings)
                self.assertTrue(all(pairs[a] == b for a, b in zip(actual, reference)))

    def test_direct_permutation_bruteforce(self):
        # All 16 sign patterns on this four-crossing three-braid projection.
        # Reference enumerates up to 20**3 complete assignments, without using
        # production arc extraction, CSP tables, propagation, or symmetry.
        for signs in itertools.product((-1, 1), repeat=4):
            word = [a * b for a, b in zip((1, 2, 1, 2), signs)]
            diagram = Diagram.from_braid(3, word)
            for order in (2, 3, 5):
                expected = reference_exists(diagram, order)
                csp = find_a5_certificate(diagram, classes=(order,), max_nodes=None)
                seed = find_a5_by_seeds(diagram, classes=(order,), max_assignments=None)
                unsymmetrized = find_a5_by_seeds(diagram, classes=(order,),
                                                max_assignments=None, symmetry=False)
                self.assertEqual(csp["status"] == "KNOTTED", expected, (word, order))
                self.assertEqual(seed["status"] == "KNOTTED", expected, (word, order))
                self.assertEqual(unsymmetrized["status"] == "KNOTTED", expected, (word, order))

    def test_unknots_never_accepted_by_palette_failure(self):
        examples = [load("hard_unknot_8"), load("unknot"), load("unknot_braid40")]
        examples.extend(Diagram.from_braid(2, [1] * k + [-1] * (k - 1)) for k in range(1, 6))
        for diagram in examples:
            for solve in (find_a5_certificate, find_a5_by_seeds):
                result = solve(diagram)
                self.assertEqual(result["status"], "INCONCLUSIVE")
                self.assertIsNone(result["certificate"])

    def test_nontrivial_a5_blind_torus_knot(self):
        # gcd(7, exponent(A5)=30)=1 forces every T(3,7) image in A5 cyclic.
        # Both exponents are odd, so this nontrivial torus knot has determinant 1.
        diagram = Diagram.from_braid(3, [1, 2] * 7)
        from fastunknot import alexander_polynomial
        from fastunknot.alexander import evaluate
        self.assertEqual(abs(evaluate(alexander_polynomial(diagram), -1)), 1)
        for solve in (find_a5_certificate, find_a5_by_seeds):
            result = solve(diagram)
            self.assertEqual(result["status"], "INCONCLUSIVE")
            self.assertEqual(result["reason"], "selected A5 palette exhausted")

    def test_row_rotation_crossing_order_mirror_invariance(self):
        rng = random.Random(314159)
        for name in ("conway", "kinoshita_terasaka", "hard_unknot_8"):
            original = load(name)
            expected = name != "hard_unknot_8"
            for mirror in (False, True):
                diagram = original.mirror() if mirror else original
                for _ in range(5):
                    rows = [row[2:] + row[:2] if rng.randrange(2) else row for row in diagram.pd]
                    rng.shuffle(rows)
                    relabel = rng.sample(range(-100, 100), 2 * diagram.crossings)
                    changed = Diagram.from_pd([[relabel[e] for e in row] for row in rows])
                    result = find_a5_by_seeds(changed, max_assignments=None)
                    self.assertEqual(result["status"] == "KNOTTED", expected)

    def test_certificate_tampering(self):
        diagram = load("conway")
        certificate = find_a5_by_seeds(diagram)["certificate"]
        corruptions = []
        altered = copy.deepcopy(certificate)
        altered["pd_sha256"] = "0" * 64
        corruptions.append(altered)
        altered = copy.deepcopy(certificate)
        altered["edge_images"][0] = [0, 1, 2, 3, 4]
        corruptions.append(altered)
        altered = copy.deepcopy(certificate)
        altered["edge_images"] = [[0, 1, 2, 3, 4] for _ in range(2 * diagram.crossings)]
        corruptions.append(altered)
        altered = copy.deepcopy(certificate)
        altered["edge_images"][0] = [1, 0, 2, 3, 4]
        corruptions.append(altered)
        altered = copy.deepcopy(certificate)
        altered["edge_images"][0] = [True, 0, 2, 3, 4]
        corruptions.append(altered)
        altered = copy.deepcopy(certificate)
        altered["noncommuting_edges"] = [0, 0]
        corruptions.append(altered)
        altered = copy.deepcopy(certificate)
        altered["noncommuting_edges"] = [-1, 0]
        corruptions.append(altered)
        corruptions.extend(({}, None, [], "not a certificate"))
        for altered in corruptions:
            self.assertFalse(verify_certificate(diagram.pd, altered)["valid"], altered)
        self.assertFalse(verify_certificate(load("kinoshita_terasaka").pd, certificate)["valid"])
        self.assertFalse(verify_certificate([[0, 1, 2, 3]], certificate)["valid"])

    def test_resource_exhaustion(self):
        diagram = load("conway")
        for options in ({"max_nodes": 0}, {"seconds": 0}, {"max_nodes": 1}):
            result = find_a5_certificate(diagram, **options)
            self.assertEqual(result["status"], "INCONCLUSIVE")
            self.assertIsNone(result["certificate"])
            self.assertIn("budget exhausted", result["reason"])
        for options in ({"max_assignments": 0}, {"seconds": 0}, {"max_assignments": 1}):
            result = find_a5_by_seeds(diagram, **options)
            self.assertEqual(result["status"], "INCONCLUSIVE")
            self.assertIsNone(result["certificate"])
            self.assertIn("budget exhausted", result["reason"])

    def test_independent_khovanov_crosscheck(self):
        rng = random.Random(1618033)
        checked = 0
        while checked < 24:
            n = rng.choice((4, 6, 8))
            word = [rng.choice((-2, -1, 1, 2)) for _ in range(n)]
            try:
                diagram = Diagram.from_braid(3, word)
            except ValueError:
                continue
            result = find_a5_by_seeds(diagram, classes=(3, 2, 5))
            rank = khovanov_rank(diagram.pd)["reduced_rank"]
            if result["status"] == "KNOTTED":
                self.assertGreater(rank, 1, word)
                self.assertTrue(verify_certificate(diagram.pd, result["certificate"])["valid"])
            if rank == 1:
                self.assertEqual(result["status"], "INCONCLUSIVE", word)
            checked += 1


if __name__ == "__main__":
    unittest.main(verbosity=2)
