#!/usr/bin/env python3
"""Independently reconstruct and verify the fixed support-consistency proof.

Standard library only. No optimizer or upstream implementation is imported.
The certificate supplies rational potentials, not trusted claims about maxima.
"""
from argparse import ArgumentParser
from fractions import Fraction
from itertools import combinations, permutations
from math import isqrt
from pathlib import Path
import copy
import json

ROOT = Path(__file__).resolve().parents[1]
EXPECTED_PLANS = [
    [[7, 4, 3, 9], [1, 6, 0], [8, 2, 5]],
    [[5, 4, 6, 7], [9, 1, 8], [2, 3, 0]],
    [[0, 5, 9, 7], [2, 1, 4], [8, 3, 6]],
    [[0, 4, 7, 8], [2, 9, 6], [1, 5, 3]],
    [[3, 1, 7, 2], [9, 6, 8], [5, 4, 0]],
    [[7, 1, 5, 8], [2, 9, 4], [0, 6, 3]],
    [[7, 2, 8, 6], [5, 9, 3], [0, 1, 4]],
    [[1, 9, 6, 7], [2, 5, 0], [4, 3, 8]],
    [[4, 6, 1, 5], [8, 9, 2], [0, 7, 3]],
]
EXPECTED_WEIGHTS = [12527, 11761, 13353, 11841, 10132, 12324, 11088, 10184, 6790]
EXPECTED_BETA_SQUARED = Fraction(283611964650596186827, 875000000000000000000)
PREVIOUS_BETA_SQUARED = Fraction(15952347164548384057, 49000000000000000000)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def fresh_supports(r, plan):
    """Build each operation directly from membership in its three vertex sets."""
    require(len(plan) == 3 and all(plan), "Three nonempty blocks required")
    require(sorted(x for block in plan for x in block) == list(range(r)),
            "Invalid group partition")
    operations = []

    def visit(block):
        if len(block) > 1:
            middle = len(block) // 2
            left, right = block[:middle], block[middle:]
            visit(left)
            visit(right)
            outside = [x for x in range(r) if x not in block]
            operations.append((left, right, outside))

    for block in plan:
        visit(block)
    operations.append(plan)
    triples = sorted(set(permutations((1400007, 1400007, 0))) |
                     set(permutations((1400000, 1175014, 750000))))
    require(len(triples) == 9, "Wrong rectangular support family")
    rows = []
    for parts in operations:
        parts = [set(part) for part in parts]
        for weights in triples:
            row = []
            for x, y in combinations(range(r), 2):
                coefficient = 0
                for (a, b), weight in zip(((0, 1), (0, 2), (1, 2)), weights):
                    if ((x in parts[a] and y in parts[b]) or
                            (y in parts[a] and x in parts[b])):
                        coefficient = weight
                row.append(coefficient)
            rows.append(tuple(row))
    require(len(rows) == 9 * (r - 2), "Wrong operation count")
    return rows


def inner(left, right):
    return sum(x * y for x, y in zip(left, right))


def sqrt_bounds(value, places=24):
    unit = 10 ** places
    lower = isqrt(value.numerator * unit * unit // value.denominator)
    require(Fraction(lower * lower, unit * unit) <= value and
            Fraction((lower + 1) ** 2, unit * unit) > value,
            "Invalid square-root enclosure")
    return Fraction(lower, unit), Fraction(lower + 1, unit)


def atan_bounds(inverse, terms=40):
    x = Fraction(1, inverse)
    partial = sum(((-1) ** j * x ** (2 * j + 1) / (2 * j + 1)
                   for j in range(terms)), Fraction(0))
    following = partial + (-1) ** terms * x ** (2 * terms + 1) / (2 * terms + 1)
    return min(partial, following), max(partial, following)


def pi_ln_bounds():
    a, b = atan_bounds(5)
    c, d = atan_bounds(239)
    pi = (16 * a - 4 * d, 16 * b - 4 * c)
    terms = 40
    lower = 2 * sum((Fraction(1, 3) ** (2 * j + 1) / (2 * j + 1)
                     for j in range(terms)), Fraction(0))
    tail = (2 * Fraction(1, 3) ** (2 * terms + 1) /
            (2 * terms + 1) / Fraction(8, 9))
    return pi, (lower, lower + tail)


def coefficient_bounds(radicals):
    pi, log_two = pi_ln_bounds()
    roots = [sqrt_bounds(value) for value in radicals]
    return (pi[0] / log_two[1] * sum(x[0] for x in roots),
            pi[1] / log_two[0] * sum(x[1] for x in roots))


def short_interval(interval):
    """Round an already proved interval outwards to a fixed rational grid."""
    unit = 10 ** 12
    low = (interval[0] * unit).numerator // (interval[0] * unit).denominator
    value = interval[1] * unit
    high = -(-value.numerator // value.denominator)
    return [str(Fraction(low, unit)), str(Fraction(high, unit))]


def verify_certificate(certificate):
    r, q = certificate["r"], certificate["q"]
    scale = certificate["support_scale"]
    weight_denominator = certificate["mixing_denominator"]
    potential_denominator = certificate["potential_denominator"]
    require((r, q, scale, weight_denominator, potential_denominator) ==
            (10, 9, 1400000, 100000, 10 ** 12), "Unexpected proof model")
    require(certificate["plans"] == EXPECTED_PLANS, "Frozen menu changed")
    require(certificate["mixing_weights"] == EXPECTED_WEIGHTS,
            "Frozen mixing weights changed")
    require(sum(EXPECTED_WEIGHTS) == weight_denominator, "Weights not normalized")
    require(Fraction(certificate["beta_squared"]) == EXPECTED_BETA_SQUARED,
            "Claimed beta squared changed")
    pairs = list(combinations(range(q), 2))
    require(certificate["pairs"] == [list(pair) for pair in pairs],
            "Unexpected pair enumeration")
    rows = [fresh_supports(r, plan) for plan in certificate["plans"]]
    require(all(len(menu) == 72 for menu in rows), "Wrong menu size")
    potentials = certificate["potentials"]
    denominator = (q - 1) * weight_denominator ** 2 * scale ** 2
    require(denominator == 156800000000000000000000,
            "Incorrect common energy denominator")
    require(denominator % potential_denominator == 0,
            "Potential denominator incompatible")
    require(set(potentials) == {f"{e},{i}" for e, pair in enumerate(pairs)
                                for i in pair}, "Missing or extra potential array")
    for i in range(q):
        incident = [e for e, pair in enumerate(pairs) if i in pair]
        for e in incident:
            values = potentials[f"{e},{i}"]
            require(len(values) == 72 and all(type(v) is int for v in values),
                    "Invalid potential array")
        for support in range(72):
            require(sum(potentials[f"{e},{i}"][support] for e in incident) == 0,
                    "Potential conservation failed")
    norms = [[inner(v, v) for v in menu] for menu in rows]
    maximum_sum = 0
    receipts = []
    for e, (i, j) in enumerate(pairs):
        wi, wj = EXPECTED_WEIGHTS[i], EXPECTED_WEIGHTS[j]

        def cost(h, k):
            return (wi * wi * norms[i][h] + wj * wj * norms[j][k]
                    + 2 * (q - 1) * wi * wj * inner(rows[i][h], rows[j][k])
                    + (potentials[f"{e},{i}"][h] + potentials[f"{e},{j}"][k])
                    * (denominator // potential_denominator))

        maximum, h, k = max((cost(h, k), h, k)
                            for h in range(72) for k in range(72))
        maximum_sum += maximum
        receipts.append({"pair": [i, j], "maximum": maximum, "witness": [h, k]})
    energy_bound = Fraction(maximum_sum, denominator)
    beta_squared = 2 * energy_bound / (r * r)
    require(beta_squared == EXPECTED_BETA_SQUARED,
            "Reconstructed support bound differs from claimed value")
    require(beta_squared < PREVIOUS_BETA_SQUARED, "No strict improvement")

    eta0 = Fraction(301, 20000)
    eta1 = Fraction(119, 10000)
    eta2 = Fraction(1549, 324000)
    root = coefficient_bounds([2 * beta_squared / eta0])
    level_one = coefficient_bounds([Fraction(7200, 301), Fraction(50304, 20111)])
    terminal = coefficient_bounds([Fraction(7200, 301), Fraction(19200, 20111),
                                   Fraction(77760, 261781)])
    require(root[1] < Fraction(29747, 1000), "Eventual bound 29.747 failed")
    require(level_one[1] < root[0] and terminal[1] < root[0],
            "Recursive branch exceeds root bound")
    require(eta0 + eta1 + eta2 / (1 - Fraction(4, 9)) == Fraction(8, 225),
            "Taper budget failed")
    require(10 ** 1000 < 2 ** 3322 and 13 ** 1000 < 2 ** 3701 and
            7 ** 100 < 2 ** 281, "Logarithm inequalities failed")
    gaps = [1 - Fraction(9, 10) - 2 * eta0 * Fraction(3322, 1000),
            1 - Fraction(9, 10) - (eta0 + eta1) * Fraction(3701, 1000),
            1 - Fraction(9, 10) - Fraction(8, 225) * Fraction(281, 100)]
    require(all(gap > 0 for gap in gaps), "Strict packing gate failed")
    require(Fraction(8, 225) * (1 + 2 * Fraction(3701, 1000)) < 1,
            "Fresh-side capacity gate failed")
    require(Fraction(3, 4) > Fraction(632, 1225), "Tail branch dominance failed")
    return {"status": "PASS", "normalization_denominator": denominator,
            "U": str(energy_bound), "beta_squared": str(beta_squared),
            "support_counts": [len(menu) for menu in rows],
            "conservation_equalities_checked": q * 72,
            "pair_choices_checked": len(pairs) * 72 * 72,
            "pair_receipts": receipts,
            "coefficients_display_only": [float(root[0]), float(level_one[0]),
                                           float(terminal[0])],
            "coefficient_rational_intervals": [short_interval(value) for value
                                                in (root, level_one, terminal)],
            "safe_eventual_time_coefficient": "29.747",
            "packing_gaps": list(map(str, gaps))}


def negative_controls(certificate):
    controls = []
    changed = copy.deepcopy(certificate)
    changed["potentials"]["0,0"][0] += 1
    controls.append((changed, "Potential conservation failed"))
    changed = copy.deepcopy(certificate)
    changed["plans"][0][0][0], changed["plans"][0][0][1] = (
        changed["plans"][0][0][1], changed["plans"][0][0][0])
    controls.append((changed, "Frozen menu changed"))
    changed = copy.deepcopy(certificate)
    changed["beta_squared"] = str(EXPECTED_BETA_SQUARED - Fraction(1, 10 ** 15))
    controls.append((changed, "Claimed beta squared changed"))
    for changed, expected_error in controls:
        try:
            verify_certificate(changed)
        except ValueError as error:
            require(str(error) == expected_error, "Unexpected negative-control failure")
        else:
            raise RuntimeError("Corrupted certificate was accepted")
    return ["nonconserved potential", "changed ordered menu", "corrupted beta squared"]


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--certificate", type=Path,
                        default=ROOT / "data" / "support_consistency_certificate.json")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    certificate = json.loads(args.certificate.read_text())
    result = verify_certificate(certificate)
    result["negative_controls"] = negative_controls(certificate)
    output = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output is None:
        print(output, end="")
    else:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(output)


if __name__ == "__main__":
    main()
