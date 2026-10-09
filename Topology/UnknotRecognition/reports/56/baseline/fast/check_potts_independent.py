"""Independent whole-cube Laurent-Jones oracle for the exact Potts code.

This test does not use Tait graphs to construct its expected values, does not
use the production ring arithmetic, and does not use a frontier scan oracle.
"""
from collections import defaultdict
from itertools import product
from math import comb
from pathlib import Path
import json
import random
import sys

FAST = Path(__file__).resolve().parent
sys.path.insert(0, str(FAST))
from fastunknot.diagram import Diagram
from fastunknot.potts_exact import potts_exact
from fastunknot.potts_factorized_exact import factorized_potts_exact


def laurent_jones(diagram):
    n, w = diagram.crossings, diagram.writhe()
    if n == 0:
        return {0: 1}
    labels = {x for row in diagram.pd for x in row}
    answer = defaultdict(int)
    for bits in range(1 << n):
        parent = {x: x for x in labels}

        def root(x):
            while parent[x] != x:
                x = parent[x]
            return x

        for i, (a, b, c, d) in enumerate(diagram.pd):
            pairs = ((a, d), (b, c)) if bits & (1 << i) else ((a, b), (c, d))
            for x, y in pairs:
                parent[root(x)] = root(y)
        circles = len({root(x) for x in labels})
        state_exponent = n - 2 * bits.bit_count()
        numerator = state_exponent - 3 * w + 2 * (circles - 1)
        assert numerator % 4 == 0
        degree = numerator // 4
        sign = (-1) ** ((w + circles - 1) % 2)
        for j in range(circles):
            answer[degree - j] += sign * comb(circles - 1, j)
    return {k: v for k, v in answer.items() if v}


def evaluate(poly, colors):
    """Reduce x^k via x^(k+2)=(colors-2)*x^(k+1)-x^k."""
    c0 = colors - 2
    lo, hi = min(poly, default=0), max(poly, default=0)
    powers = {0: (1, 0), 1: (0, 1)}
    for k in range(2, hi + 1):
        a, b = powers[k - 1]
        c, d = powers[k - 2]
        powers[k] = (c0 * a - c, c0 * b - d)
    for k in range(-1, lo - 1, -1):
        a, b = powers[k + 1]
        c, d = powers[k + 2]
        powers[k] = (c0 * a - c, c0 * b - d)
    return tuple(sum(coefficient * powers[k][j] for k, coefficient in poly.items())
                 for j in (0, 1))


def times(left, right, colors):
    """Polynomial convolution followed by a separate reduction of x^2."""
    raw = [0, 0, 0]
    for i, x in enumerate(left):
        for j, y in enumerate(right):
            raw[i + j] += x * y
    return (raw[0] - raw[2], raw[1] + (colors - 2) * raw[2])


def main():
    rng = random.Random(608102026)
    cases = []
    attempted = 0
    for strands, length in [(2, 1), (2, 3), (2, 5), (3, 2), (3, 4)]:
        alphabet = tuple(i for i in range(1, strands)) + tuple(-i for i in range(1, strands))
        for word in product(alphabet, repeat=length):
            attempted += 1
            try:
                cases.append(Diagram.from_braid(strands, word))
            except ValueError:
                pass
    for strands, length, count in [(3, 8, 12), (4, 9, 12), (5, 10, 8)]:
        accepted = 0
        while accepted < count:
            word = [rng.choice((-1, 1)) * rng.randrange(1, strands) for _ in range(length)]
            attempted += 1
            try:
                cases.append(Diagram.from_braid(strands, word))
            except ValueError:
                continue
            accepted += 1
    cases.extend(Diagram.from_braid(s, [j for j in range(1, s) for _ in range(3)])
                 for s in (3, 4, 5))
    sources = []
    for name in ("conway", "kinoshita_terasaka", "hard_unknot_8"):
        path = FAST / "examples" / (name + ".json")
        if path.exists():
            diagram = Diagram.from_json(json.loads(path.read_text()))
            if diagram.crossings <= 12:
                cases.append(diagram)
                sources.append(name)

    comparisons = factorized_comparisons = state_count = 0
    maxima = dict(crossings=0, boundary=0, spin_frontier=0, coefficient_bits=0)
    for diagram in cases:
        poly = laurent_jones(diagram)
        state_count += 1 << diagram.crossings
        orders = [list(range(diagram.crossings)), list(reversed(range(diagram.crossings)))]
        shuffled = list(range(diagram.crossings))
        rng.shuffle(shuffled)
        orders.append(shuffled)
        for colors in (5, 6, 7):
            expected_jones = evaluate(poly, colors)
            for order in orders:
                for shade in (0, 1):
                    got = potts_exact(diagram, colors=colors, order=order, shade=shade,
                                      max_states=None, max_transitions=None)
                    assert tuple(got["partition_function"]) == times(
                        expected_jones, got["unknot_partition"], colors), (
                            diagram.pd, order, shade, got, poly)
                    assert got["differs"] == (expected_jones != (1, 0))
                    bound = (colors ** got["tait_vertices"] *
                             (colors - 1) ** diagram.crossings).bit_length()
                    assert got["max_coefficient_bits"] <= bound
                    if colors in (5, 6):
                        assert got["max_coefficient_bits"] <= 5 * diagram.crossings + 4
                    factored = factorized_potts_exact(diagram, colors=colors, order=order,
                                                      shade=shade, max_states=None,
                                                      max_transitions=None)
                    assert tuple(factored["partition_function"]) == times(
                        expected_jones, factored["unknot_partition"], colors)
                    assert factored["differs"] == (expected_jones != (1, 0))
                    assert factored["max_coefficient_bits"] <= bound
                    assert factored["max_component_frontier"] <= factored["max_spin_frontier"]
                    factorized_comparisons += 1
                    maxima["crossings"] = max(maxima["crossings"], diagram.crossings)
                    maxima["boundary"] = max(maxima["boundary"], got["max_boundary"])
                    maxima["spin_frontier"] = max(maxima["spin_frontier"], got["max_spin_frontier"])
                    maxima["coefficient_bits"] = max(maxima["coefficient_bits"], got["max_coefficient_bits"])
                    comparisons += 1

    weaving = []
    for m in (1, 2, 4, 5, 7, 8, 10, 11, 13, 14, 16, 17, 25, 31, 49):
        diagram = Diagram.from_braid(3, [1, -2] * m)
        for colors in (5, 6, 7):
            trace0, trace1 = 2, 3 - colors
            for _ in range(1, m):
                trace0, trace1 = trace1, (3 - colors) * trace1 - trace0
            value = colors - 2 + trace1
            got = potts_exact(diagram, colors=colors, order=list(range(diagram.crossings)),
                              max_states=None, max_transitions=None)
            assert got["partition_function"] == [value * x for x in got["unknot_partition"]]
            assert got["differs"] == (value != 1)
            assert got["differs"] == (m > 1 and (colors >= 6 or m % 2 == 0))
            factored = factorized_potts_exact(diagram, colors=colors,
                                              order=list(range(diagram.crossings)),
                                              max_states=None, max_transitions=None)
            assert factored["partition_function"] == [value * x for x in factored["unknot_partition"]]
            assert factored["differs"] == got["differs"]
            weaving.append(dict(m=m, q=colors, normalized_value=value,
                                differs=got["differs"], factorized_checked=True))
    result = dict(status="PASS", seed=608102026, diagrams=len(cases),
                  attempted_braid_words=attempted, exact_cube_states=state_count,
                  shade_and_order_comparisons=comparisons, fixture_names=sources,
                  factorized_shade_and_order_comparisons=factorized_comparisons,
                  colors=[5, 6, 7], maxima=maxima, weaving_checks=weaving,
                  scope="Independent full-state Laurent polynomial versus exact quadratic Potts")
    Path(sys.argv[1]).write_text(
        json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
