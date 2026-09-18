"""Tests for fastunknot.  Run from the project root: python -m unittest discover -s tests -v"""
from __future__ import annotations

import json
import os
import random
import subprocess
import sys
import unittest

ROOT = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "fast")
sys.path.insert(0, ROOT)

from fastunknot import Diagram, DiagramError, alexander_polynomial, khovanov_rank, recognize  # noqa: E402
from fastunknot.alexander import determinant, evaluate, exact_div, mul  # noqa: E402
from fastunknot.scan import ScanComplex, compose, inverse, is_unit, order_profile, scan_order  # noqa: E402
from fastunknot.simplify import apply_move, descending_start, legal_moves, simplify  # noqa: E402

# Exercise the old pipeline configuration explicitly. The new default has
# additional sound screens; command-line tests below disable those too.
_accelerated_recognize = recognize
def recognize(*args, **kwargs):
    kwargs.setdefault("use_jones", False)
    kwargs.setdefault("use_factor", False)
    return _accelerated_recognize(*args, **kwargs)

EXAMPLES = os.path.join(ROOT, "examples")


def load(name):
    with open(os.path.join(EXAMPLES, name), encoding="utf-8") as handle:
        return Diagram.from_json(json.load(handle))


def one_component(strands, word):
    p = list(range(strands))
    for g in word:
        i = abs(g) - 1
        p[i], p[i + 1] = p[i + 1], p[i]
    seen, count = set(), 0
    for s in range(strands):
        if s in seen:
            continue
        count += 1
        x = s
        while x not in seen:
            seen.add(x)
            x = p[x]
    return count == 1


def reference_reduced_rank(diagram: Diagram) -> int:
    """Independent dense cube-of-resolutions computation (reduced, F2)."""
    n = diagram.crossings
    if n == 0:
        return 1
    pd = diagram.pd

    def circles(state):
        parent = list(range(2 * n))

        def find(x):
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x

        for i, (a, b, c, d) in enumerate(pd):
            pairs = ((a, d), (b, c)) if state >> i & 1 else ((a, b), (c, d))
            for x, y in pairs:
                parent[find(x)] = find(y)
        groups = {}
        for e in range(2 * n):
            groups.setdefault(find(e), []).append(e)
        comps = sorted(groups.values())
        owner = {}
        for k, comp in enumerate(comps):
            for e in comp:
                owner[e] = k
        return comps, owner

    data = [circles(s) for s in range(1 << n)]
    # generators: (state, labels tuple with labels[owner[0]] == 1 (x))
    generators = {}
    by_degree = {}
    for s in range(1 << n):
        comps, owner = data[s]
        k = len(comps)
        marked = owner[0]
        for bits in range(1 << k):
            labels = tuple((bits >> j) & 1 for j in range(k))
            if labels[marked] != 1:
                continue
            index = len(generators)
            generators[s, labels] = index
            by_degree.setdefault(bin(s).count("1"), []).append((s, labels))
    columns = {}
    for (s, labels), index in generators.items():
        comps, owner = data[s]
        image = set()
        for i in range(n):
            if s >> i & 1:
                continue
            t = s | (1 << i)
            comps_t, owner_t = data[t]
            out = [None] * len(comps_t)
            src_changed = [j for j, comp in enumerate(comps) if comp not in comps_t]
            tgt_changed = [j for j, comp in enumerate(comps_t) if comp not in comps]
            for j, comp in enumerate(comps):
                if comp in comps_t:
                    out[comps_t.index(comp)] = labels[j]
            if len(src_changed) == 2:
                a, b = (labels[j] for j in src_changed)
                if a and b:
                    continue
                out[tgt_changed[0]] = a | b
                candidates = [tuple(out)]
            else:
                a = labels[src_changed[0]]
                j, k = tgt_changed
                candidates = []
                if a:
                    o = list(out)
                    o[j] = o[k] = 1
                    candidates.append(tuple(o))
                else:
                    for j1, k1 in ((0, 1), (1, 0)):
                        o = list(out)
                        o[j], o[k] = j1, k1
                        candidates.append(tuple(o))
            for cand in candidates:
                key = (t, cand)
                if key in generators:
                    image ^= {generators[key]}
        columns[index] = image
    # rank of d over F2 by elimination on sets
    total_rank = 0
    for h, gens in by_degree.items():
        pivots = {}
        for s, labels in gens:
            col = set(columns[generators[s, labels]])
            while col:
                p = max(col)
                if p in pivots:
                    col ^= pivots[p]
                else:
                    pivots[p] = col
                    break
        total_rank += len(pivots)
    return len(generators) - 2 * total_rank


class DiagramTests(unittest.TestCase):
    def test_invalid_inputs(self):
        for bad in ([[1, 2, 3]], [[1, 2, 3, 4]], [[1, 2, 1, 3], [3, 2, 4, 4]]):
            with self.assertRaises(DiagramError):
                Diagram.from_pd(bad)
        with self.assertRaises(DiagramError):
            Diagram.from_braid(3, [1])          # two components
        with self.assertRaises(DiagramError):
            Diagram.from_braid(2, [2])
        with self.assertRaises(DiagramError):
            Diagram.from_pd([[0, 1, 2, 3], [1, 0, 3, 2]])  # link with two components

    def test_virtual_rejected(self):
        # a rotation system on the torus: the abstract graph is planar but this embedding is not
        with self.assertRaises(DiagramError):
            Diagram.from_pd([[0, 1, 2, 3], [2, 1, 0, 3]])

    def test_grid_conversion(self):
        grid = load("grid_determinant_one_knot.json")
        self.assertEqual(grid.crossings, 10)
        self.assertEqual(alexander_polynomial(grid), alexander_polynomial(load("torus_3_5.json")))
        self.assertEqual(recognize(load("grid_scrambled_unknot.json")).status, "UNKNOT")

    def test_signs_and_writhe(self):
        self.assertEqual(abs(Diagram.from_braid(2, [1, 1, 1]).writhe()), 3)
        self.assertEqual(Diagram.from_braid(3, [1, -2, 1, -2]).writhe(), 0)
        self.assertEqual(Diagram.from_braid(2, [1, 1, 1]).mirror().writhe(),
                         -Diagram.from_braid(2, [1, 1, 1]).writhe())


class AlexanderTests(unittest.TestCase):
    def test_polynomial_arithmetic(self):
        self.assertEqual(mul([1, 1], [1, -1]), [1, 0, -1])
        self.assertEqual(exact_div([1, 0, -1], [1, 1]), [1, -1])
        with self.assertRaises(ArithmeticError):
            exact_div([1, 1, 1], [1, 1])
        self.assertEqual(determinant([[[2], [1]], [[1], [3]]]), [5])
        self.assertEqual(determinant([[[0, 1], [1]], [[1], [0, 1]]]), [-1, 0, 1])

    def test_known_polynomials(self):
        self.assertEqual(alexander_polynomial(Diagram.from_braid(2, [1, 1, 1])), [1, -1, 1])
        self.assertEqual(alexander_polynomial(Diagram.from_braid(3, [1, -2, 1, -2])), [1, -3, 1])
        self.assertEqual(alexander_polynomial(Diagram.from_braid(3, [1, 1, 1, 2, -1, 2])), [2, -3, 2])
        self.assertEqual(alexander_polynomial(Diagram.from_braid(3, [1, 2] * 5)),
                         [1, -1, 0, 1, -1, 1, 0, -1, 1])
        for name in ("kinoshita_terasaka.json", "conway.json", "hard_unknot_8.json", "unknot.json"):
            self.assertEqual(alexander_polynomial(load(name)), [1], name)

    def test_symmetry_and_determinant(self):
        rng = random.Random(5)
        for _ in range(40):
            strands = rng.choice([3, 4])
            word = [rng.choice([-1, 1]) * rng.randint(1, strands - 1) for _ in range(rng.randint(4, 10))]
            if not one_component(strands, word):
                continue
            d = Diagram.from_braid(strands, word)
            p = alexander_polynomial(d)
            self.assertEqual(p, p[::-1])
            self.assertEqual(abs(evaluate(p, 1)), 1)
            self.assertEqual(p, alexander_polynomial(d.mirror()))
            self.assertEqual(evaluate(p, -1) % 2, 1)


class SimplifyTests(unittest.TestCase):
    def test_reidemeister_moves(self):
        curl = Diagram.from_braid(2, [1])
        reduced, trace = simplify(curl)
        self.assertEqual(reduced.crossings, 0)
        self.assertEqual([m.kind for m in trace], ["R1"])
        pair = Diagram.from_braid(3, [1, -1, 2, 1])
        self.assertTrue(any(m.kind == "R2" for m in legal_moves(pair)))
        reduced, trace = simplify(pair)
        self.assertEqual(reduced.crossings, 0)
        clasp = Diagram.from_braid(2, [1, 1, 1])
        self.assertEqual(legal_moves(clasp), [])
        with self.assertRaises(ValueError):
            apply_move(clasp, trace[0])
        # bigons of the trefoil closure are clasps (over then under): no Reidemeister II
        self.assertEqual([m.kind for m in legal_moves(clasp)], [])

    def test_descending(self):
        self.assertIsNotNone(descending_start(Diagram.from_braid(3, [1, 2])))
        self.assertIsNone(descending_start(Diagram.from_braid(2, [1, 1, 1])))


class ScanAlgebraTests(unittest.TestCase):
    def test_end_ring_is_local(self):
        m = frozenset({frozenset({0, 1}), frozenset({2, 3})})
        one = {frozenset()}
        x0 = {frozenset({frozenset({0, 1})})}
        self.assertEqual(compose(x0, x0, m, m, m), set())          # x^2 = 0
        self.assertEqual(compose(one, x0, m, m, m), x0)
        unit = one | x0
        self.assertTrue(is_unit(unit))
        self.assertEqual(compose(unit, inverse(unit, m), m, m, m), one)
        self.assertFalse(is_unit(x0))

    def test_d_squared_during_scan(self):
        for strands, word in ((3, [1, 2] * 4), (4, [1, -2, 3, -2, 1, 3, 2]), (3, [-2, -2, -2, 2, 1, 1, 2, 1])):
            d = Diagram.from_braid(strands, word)
            khovanov_rank(d.pd, check_d_squared=True)

    def test_order_independence(self):
        rng = random.Random(11)
        d = Diagram.from_braid(4, [1, 2, -3, 2, 1, -3, 2, 2, 1])
        reference = khovanov_rank(d.pd)["rank"]
        for _ in range(5):
            order = list(range(d.crossings))
            rng.shuffle(order)
            self.assertEqual(khovanov_rank(d.pd, order=order)["rank"], reference)

    def test_scan_order_profile(self):
        d = Diagram.from_braid(41, list(range(1, 41)))
        order = scan_order(d.pd)
        self.assertEqual(sorted(order), list(range(40)))
        self.assertLessEqual(order_profile(d.pd, order)[0], 4)

    def test_limits_give_no_verdict(self):
        d = Diagram.from_braid(3, [1, 2] * 5)
        with self.assertRaises(Exception):
            khovanov_rank(d.pd, max_objects=3)
        result = recognize(d, max_objects=3, use_alexander=False)
        self.assertEqual(result.status, "UNKNOWN")
        self.assertIsNone(result.is_unknot)
        self.assertEqual(recognize(d, seconds=0.0, use_alexander=False).status, "UNKNOWN")


class RankTests(unittest.TestCase):
    def test_named_ranks(self):
        expected = {"unknot.json": 1, "trefoil.json": 3, "figure_eight.json": 5, "torus_3_5.json": 7,
                    "hard_unknot_8.json": 1, "kinoshita_terasaka.json": 33, "conway.json": 33,
                    "unknot_braid40.json": 1, "grid_determinant_one_knot.json": 7}
        for name, rank in expected.items():
            self.assertEqual(khovanov_rank(load(name).pd)["reduced_rank"], rank, name)

    def test_against_independent_cube(self):
        rng = random.Random(3)
        checked = 0
        while checked < 25:
            strands = rng.choice([3, 4])
            word = [rng.choice([-1, 1]) * rng.randint(1, strands - 1) for _ in range(rng.randint(3, 8))]
            if not one_component(strands, word):
                continue
            d = Diagram.from_braid(strands, word)
            self.assertEqual(khovanov_rank(d.pd)["reduced_rank"], reference_reduced_rank(d), word)
            checked += 1

    def test_two_strand_family(self):
        for e in range(1, 12, 2):
            d = Diagram.from_braid(2, [1] * e)
            self.assertEqual(khovanov_rank(d.pd)["reduced_rank"], e)
            self.assertEqual(recognize(d).status, "UNKNOT" if e == 1 else "KNOTTED")


class PipelineTests(unittest.TestCase):
    def test_methods(self):
        self.assertEqual(recognize(Diagram.from_braid(2, [1])).method, "reidemeister-reduction")
        self.assertEqual(recognize(Diagram.from_braid(3, [1, 2]), use_reduction=False).method,
                         "descending-diagram")
        # (sigma_1 sigma_2)^2 closes to a trefoil, not an unknot
        self.assertEqual(recognize(Diagram.from_braid(3, [1, 2, 1, 2])).status, "KNOTTED")
        self.assertEqual(recognize(Diagram.from_braid(2, [1, 1, 1])).method, "alexander-polynomial")
        r = recognize(load("torus_3_5.json"))
        self.assertEqual((r.status, r.method), ("KNOTTED", "alexander-polynomial"))
        r = recognize(load("conway.json"))
        self.assertEqual((r.status, r.method), ("KNOTTED", "reduced-khovanov-F2-scan"))
        r = recognize(load("hard_unknot_8.json"), use_reduction=False, use_descending=False)
        self.assertEqual((r.status, r.method), ("UNKNOT", "reduced-khovanov-F2-scan"))
        self.assertFalse(r.to_json()["quasipolynomial_guarantee"])

    def test_cli(self):
        env = dict(os.environ, PYTHONPATH=ROOT)
        run = lambda *args: subprocess.run([sys.executable, "-m", "fastunknot", *args], cwd=ROOT,
                                           capture_output=True, text=True, env=env)
        out = run("recognize", os.path.join(EXAMPLES, "trefoil.json"))
        self.assertEqual(out.returncode, 0)
        self.assertEqual(json.loads(out.stdout)["status"], "KNOTTED")
        out = run("recognize", os.path.join(EXAMPLES, "conway.json"), "--no-alexander", "--no-jones", "--no-factor", "--max-objects", "2")
        self.assertEqual(out.returncode, 3)
        self.assertEqual(json.loads(out.stdout)["status"], "UNKNOWN")
        self.assertEqual(run("recognize", os.path.join(EXAMPLES, "missing.json")).returncode, 2)
        out = run("alexander", os.path.join(EXAMPLES, "figure_eight.json"))
        self.assertEqual(json.loads(out.stdout)["coefficients"], [1, -3, 1])


if __name__ == "__main__":
    unittest.main()
