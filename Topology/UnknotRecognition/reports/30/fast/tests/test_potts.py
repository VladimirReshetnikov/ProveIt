"""Independent checks for the signed-Tait five-spin Jones specialization."""
import itertools
import json
from pathlib import Path
import random
import unittest
from unittest.mock import patch

from fastunknot.diagram import Diagram, DiagramError
from fastunknot.filters import FilterLimit, PRIME, jones_obstruction
from fastunknot.geometry import SMOOTHINGS
from fastunknot.ordering import best_scan_order
from fastunknot.potts import (COLORS, POTTS_A, POTTS_DELTA, POTTS_X,
                             _extensions, _schedule, potts_bracket,
                             potts_obstruction, tait_graph)


EXAMPLES = Path(__file__).resolve().parents[1] / "examples"


def brute_bracket(diagram):
    """The complete smoothing cube, without Tait graphs or frontier code."""
    if not diagram.pd:
        return POTTS_DELTA
    n = diagram.crossings
    answer = 0
    for smoothing in itertools.product((0, 1), repeat=n):
        parent = list(range(2 * n))

        def find(x):
            while parent[x] != x:
                x = parent[x]
            return x

        for row, choice in zip(diagram.pd, smoothing):
            for a, b in SMOOTHINGS[choice]:
                ra, rb = find(row[a]), find(row[b])
                parent[ra] = rb
        circles = len({find(x) for x in range(2 * n)})
        answer += pow(POTTS_A, n - 2 * sum(smoothing), PRIME) * pow(
            POTTS_DELTA, circles, PRIME)
    return answer % PRIME


def brute_labeled_spins(vertices, edges):
    """All 5^v assignments, independent of equality-pattern aggregation."""
    weights = {1: (-pow(POTTS_X, -1, PRIME)) % PRIME,
               -1: (-POTTS_X) % PRIME}
    total = 0
    for colors in itertools.product(range(COLORS), repeat=vertices):
        term = 1
        for u, v, exponent in edges:
            if colors[u] == colors[v]:
                term = term * weights[exponent] % PRIME
        total += term
    return total % PRIME


def brute_fk(vertices, edges):
    """All edge subsets in the multivariate random-cluster expansion."""
    activities = {1: (-1 - pow(POTTS_X, -1, PRIME)) % PRIME,
                  -1: (-1 - POTTS_X) % PRIME}
    total = 0
    for subset in range(1 << len(edges)):
        parent = list(range(vertices))

        def find(x):
            while parent[x] != x:
                x = parent[x]
            return x

        term = 1
        for i, (u, v, exponent) in enumerate(edges):
            if subset >> i & 1:
                parent[find(u)] = find(v)
                term = term * activities[exponent] % PRIME
        components = len({find(v) for v in range(vertices)})
        total += term * pow(COLORS, components, PRIME)
    return total % PRIME


def random_knots(count, seed=251007, max_crossings=10):
    rng = random.Random(seed)
    result = []
    while len(result) < count:
        strands = rng.randrange(2, 6)
        length = rng.randrange(1, max_crossings + 1)
        word = [rng.choice((-1, 1)) * rng.randrange(1, strands)
                for _ in range(length)]
        try:
            result.append(Diagram.from_braid(strands, word))
        except DiagramError:
            pass
    return result


class PottsTests(unittest.TestCase):
    def test_specialization(self):
        self.assertEqual(pow(POTTS_A, 4, PRIME), POTTS_X)
        self.assertEqual((POTTS_X * POTTS_X - 3 * POTTS_X + 1) % PRIME, 0)
        self.assertEqual(POTTS_DELTA * POTTS_DELTA % PRIME, COLORS)

    def test_empty_circle_and_zero_budgets(self):
        diagram = Diagram.from_pd([])
        self.assertIsNone(potts_obstruction(diagram, max_states=0, max_transitions=0))
        self.assertEqual(potts_bracket(diagram)["partition_function"], 5)
        self.assertEqual(tait_graph(diagram), (1, ()))
        for keyword in ("max_states", "max_transitions"):
            with self.assertRaises(FilterLimit):
                potts_obstruction(Diagram.from_braid(2, [1]), **{keyword: 0})

    def test_invalid_budgets_orders_and_shades(self):
        diagram = Diagram.from_braid(2, [1, 1, 1])
        for keyword in ("max_states", "max_transitions"):
            for value in (-1, 0.5, True):
                with self.assertRaises(ValueError):
                    potts_bracket(diagram, **{keyword: value})
        for order in ([0], [0, 0, 1], [0, 1, 3], [False, 1, 2]):
            with self.assertRaises(ValueError):
                potts_bracket(diagram, order=order)
        for shade in (-1, 2, True, "auto"):
            with self.assertRaises(ValueError):
                potts_bracket(diagram, shade=shade)

    def test_cooperative_resource_exception_propagates(self):
        class Stop(Exception):
            pass

        def check():
            raise Stop("caller deadline")

        with self.assertRaises(Stop):
            potts_obstruction(Diagram.from_braid(2, [1]), check=check)

    def test_color_orbit_extension_multiplicities(self):
        for used in range(6):
            state = tuple(range(used))
            for introduced in range(3):
                patterns = _extensions(state, introduced)
                self.assertEqual(sum(m for _, m, _ in patterns), 5 ** introduced)
                self.assertEqual(len({p for p, _, _ in patterns}), len(patterns))
                self.assertTrue(all(max(p, default=-1) < 5 for p, _, _ in patterns))

    def test_loops_parallel_edges_and_raw_spins(self):
        cases = [Diagram.from_braid(2, [1]), Diagram.from_braid(2, [-1]),
                 Diagram.from_braid(2, [1, 1, 1]),
                 Diagram.from_braid(2, [1, -1, 1]),
                 Diagram.from_braid(3, [1, -2, 1, -2])]
        saw_loop = saw_parallel = False
        for diagram in cases:
            for shade in (0, 1):
                vertices, edges = tait_graph(diagram, shade=shade)
                saw_loop |= any(u == v for u, v, _ in edges)
                pairs = [tuple(sorted((u, v))) for u, v, _ in edges]
                saw_parallel |= len(pairs) != len(set(pairs))
                result = potts_bracket(diagram, shade=shade,
                                       order=list(reversed(range(diagram.crossings))))
                self.assertEqual(result["partition_function"],
                                 brute_labeled_spins(vertices, edges))
                self.assertEqual(result["partition_function"], brute_fk(vertices, edges))
                self.assertEqual(result["bracket"], brute_bracket(diagram))
        self.assertTrue(saw_loop)
        self.assertTrue(saw_parallel)

    def test_random_cube_fk_and_checkerboard_duality(self):
        rng = random.Random(4821)
        for diagram in random_knots(160):
            expected = brute_bracket(diagram)
            order = list(range(diagram.crossings))
            rng.shuffle(order)
            for shade in (0, 1):
                vertices, edges = tait_graph(diagram, shade=shade)
                result = potts_bracket(diagram, shade=shade, order=order,
                                       max_states=None, max_transitions=None)
                self.assertEqual(result["bracket"], expected)
                self.assertEqual(result["partition_function"], brute_fk(vertices, edges))
                self.assertLessEqual(2 * result["max_spin_frontier"],
                                     result["max_boundary"])

    def test_all_crossing_orders_on_figure_eight(self):
        diagram = Diagram.from_braid(3, [1, -2, 1, -2])
        expected = brute_bracket(diagram)
        for order in itertools.permutations(range(4)):
            for shade in (None, 0, 1):
                self.assertEqual(potts_bracket(diagram, order=order, shade=shade)["bracket"],
                                 expected)

    def test_mirrors_and_arbitrary_under_port_choices(self):
        rng = random.Random(1013)
        for diagram in random_knots(60, seed=721301, max_crossings=9):
            changed = Diagram.from_pd([row[2:] + row[:2] if rng.randrange(2) else row
                                       for row in diagram.pd])
            self.assertEqual(potts_bracket(changed)["bracket"],
                             potts_bracket(diagram)["bracket"])
            self.assertEqual(potts_bracket(diagram.mirror())["bracket"],
                             brute_bracket(diagram.mirror()))

    def test_named_corpus_against_original_jones_geometry(self):
        with patch("fastunknot.filters.JONES_A", POTTS_A):
            for path in sorted(EXAMPLES.glob("*.json")):
                diagram = Diagram.from_json(json.loads(path.read_text()))
                stats = {}
                result = potts_bracket(diagram, statistics=stats)
                self.assertEqual(stats, result)
                legacy = jones_obstruction(diagram)
                expected = legacy["bracket"] if legacy else result["unknot_bracket"]
                self.assertEqual(result["bracket"], expected, path.name)
                witness = potts_obstruction(diagram)
                self.assertEqual(witness is not None, legacy is not None, path.name)
                if witness is not None:
                    self.assertEqual(witness["kind"], "potts-jones-differs-from-unknot")

    def test_budget_boundary_is_replayable(self):
        diagram = Diagram.from_braid(3, [1, -2, 1, -2])
        result = potts_bracket(diagram)
        self.assertEqual(potts_bracket(diagram, max_transitions=result["transitions"]),
                         result)
        with self.assertRaises(FilterLimit):
            potts_bracket(diagram, max_transitions=result["transitions"] - 1)
        with self.assertRaises(FilterLimit):
            potts_bracket(diagram, max_states=1)

    def test_auto_shade_uses_same_order_profile(self):
        for diagram in random_knots(80, seed=33179, max_crossings=20):
            order = best_scan_order(diagram.pd)
            profiles = []
            for shade in (0, 1):
                vertices, edges = tait_graph(diagram, shade=shade)
                profiles.append(_schedule(vertices, edges, order)[2])
            result = potts_bracket(diagram, order=order)
            chosen = min(range(2), key=lambda shade: (profiles[shade], shade))
            self.assertEqual(result["shade"], chosen)
            self.assertEqual(result["max_spin_frontier"], profiles[chosen][0])


if __name__ == "__main__":
    unittest.main()
