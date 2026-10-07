#!/usr/bin/env python3
"""Exact finite audits for the Section 14 counting refinements.

No third-party packages are needed.  The general theorems are proved in
the article; these checks audit ordered parameterization, target torsion,
vertex multiplicity, the weighted two-orientation identity, and exponent
arithmetic.  All inequalities are checked with integers or Fractions.

Usage:
    python code/verify_counting.py
    python code/verify_counting.py --output verification-counting.json
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
from fractions import Fraction
from pathlib import Path


def prod(values):
    return math.prod(values)


def points(moduli):
    return list(itertools.product(*(range(n) for n in moduli)))


def vertex(base, side, eps, moduli):
    return tuple((x + e * h) % n for x, h, e, n
                 in zip(base, side, eps, moduli))


def mixed(labels, ids, signs, target):
    return sum(sign * labels[i] for i, sign in zip(ids, signs)) % target


def mask_of(ids):
    mask = 0
    for i in ids:
        mask |= 1 << i
    return mask


def build_case(moduli, target):
    """Precompute all pairs, configurations, and gluing source records."""
    k = len(moduli)
    pts = points(moduli)
    index = {point: i for i, point in enumerate(pts)}
    size = len(pts)
    epss = list(itertools.product((0, 1), repeat=k))
    signs = [(-1) ** sum(eps) for eps in epss]
    cubes = {}
    for x in pts:
        for h in pts:
            cubes[x, h] = tuple(index[vertex(x, h, eps, moduli)]
                                for eps in epss)

    # w_i = (i+1)^(2^(k-1)), so w_i^(2^(1-k)) is an integer.
    weight_roots = tuple(range(1, size + 1))
    weights = tuple(a ** (2 ** (k - 1)) for a in weight_roots)
    pairs = []
    pair_index = {}
    for x in pts:
        for y in pts:
            for h in pts:
                left, right = cubes[x, h], cubes[y, h]
                pair_index[x, y, h] = len(pairs)
                pairs.append({
                    "left": left,
                    "right": right,
                    "mask": mask_of(left + right),
                    "weight": prod(weights[i] for i in left + right),
                })

    horizontal_moduli, n = moduli[:-1], moduli[-1]
    horizontal = points(horizontal_moduli)
    hepss = list(itertools.product((0, 1), repeat=k - 1))
    hsigns = [(-1) ** sum(eps) for eps in hepss]
    records = []
    first_outputs, second_outputs = [], []
    for x in horizontal:
        for y in horizontal:
            for h in horizontal:
                left_levels, right_levels = [], []
                for u in range(n):
                    left_levels.append(tuple(
                        index[vertex(x, h, eps, horizontal_moduli) + (u,)]
                        for eps in hepss))
                    right_levels.append(tuple(
                        index[vertex(y, h, eps, horizontal_moduli) + (u,)]
                        for eps in hepss))
                for a, c, d in itertools.product(range(n), repeat=3):
                    b = (c + d - a) % n
                    t = (c - a) % n
                    levels = (a, b, c, d)
                    left = tuple(left_levels[u] for u in levels)
                    right = tuple(right_levels[u] for u in levels)
                    flat = tuple(i for layer in left + right for i in layer)
                    p1 = pair_index[x + (a,), y + (d,), h + (t,)]
                    p2 = pair_index[y + (a,), x + (d,), h + (t,)]
                    first_outputs.append(p1)
                    second_outputs.append(p2)
                    ps = [prod(weights[i] for i in layer) for layer in left]
                    qs = [prod(weights[i] for i in layer) for layer in right]
                    theta = []
                    for p, q in zip(ps, qs):
                        root = math.isqrt(p * q)
                        assert root * root == p * q
                        theta.append(root)
                    theta_product = prod(theta)
                    u = ps[0] * ps[2] * qs[3] * qs[1]
                    u_prime = qs[0] * qs[2] * ps[3] * ps[1]
                    assert u == pairs[p1]["weight"]
                    assert u_prime == pairs[p2]["weight"]
                    assert theta_product ** 2 == u * u_prime
                    records.append({
                        "left": left,
                        "right": right,
                        "mask": mask_of(flat),
                        "p1": p1,
                        "p2": p2,
                        "theta": theta_product,
                    })

    # Each orientation is actually a bijection on all ambient parameters.
    assert len(records) == size ** 3
    assert sorted(first_outputs) == list(range(size ** 3))
    assert sorted(second_outputs) == list(range(size ** 3))

    configs = []
    states = list(itertools.product(range(4), repeat=k))
    state_index = {state: i for i, state in enumerate(states)}
    state_bits = ((0, 0), (1, 0), (0, 1), (1, 1))
    for x, g, h in itertools.product(pts, repeat=3):
        ids = []
        for state in states:
            v = tuple((xj + state_bits[s][0] * gj
                       + state_bits[s][1] * hj) % n
                      for xj, gj, hj, s, n in zip(x, g, h, state, moduli))
            ids.append(index[v])
        faces = []
        for j in range(k):
            for rest in itertools.product(range(4), repeat=k - 1):
                face = []
                for sj in range(4):
                    state = rest[:j] + (sj,) + rest[j:]
                    face.append(ids[state_index[state]])
                faces.append(tuple(face))
        configs.append({
            "mask": mask_of(ids),
            "faces": faces,
            "weight": prod(weights[i] for i in ids),
        })

    return {
        "moduli": moduli, "target": target, "k": k, "size": size,
        "signs": signs, "hsigns": hsigns, "pairs": pairs,
        "records": records, "configs": configs, "weights": weights,
        "roots": weight_roots,
    }


def verify_map(case, labels, weighted):
    target, size, k = case["target"], case["size"], case["k"]
    present = sum(1 << i for i, value in enumerate(labels) if value >= 0)
    pair_ok = []
    for pair in case["pairs"]:
        ok = pair["mask"] & present == pair["mask"]
        if ok:
            ok = (mixed(labels, pair["left"], case["signs"], target)
                  == mixed(labels, pair["right"], case["signs"], target))
        pair_ok.append(ok)
    count = sum(pair_ok)
    e = 4 * (4 ** k - 2 ** k)
    assert e % 8 == 0
    support_size = present.bit_count()
    # Every partial map to Z/q has PP_(q^(-1/8)).
    assert count * target ** (e // 8) * size ** (4 ** k) >= (
        size ** 3 * support_size ** (4 ** k))

    admitted_count = 0
    total_u = total_u_prime = total_theta = 0
    for record in case["records"]:
        if record["mask"] & present != record["mask"]:
            continue
        left, right = record["left"], record["right"]
        if any(mixed(labels, l, case["hsigns"], target)
               != mixed(labels, r, case["hsigns"], target)
               for l, r in zip(left, right)):
            continue
        if any((labels[left[0][j]] + labels[left[1][j]]
                - labels[left[2][j]] - labels[left[3][j]]) % target
               for j in range(2 ** (k - 1))):
            continue
        admitted_count += 1
        assert pair_ok[record["p1"]]
        assert pair_ok[record["p2"]]
        if weighted:
            total_u += case["pairs"][record["p1"]]["weight"]
            total_u_prime += case["pairs"][record["p2"]]["weight"]
            total_theta += record["theta"]
    assert admitted_count <= count

    if weighted:
        c_weight = sum(pair["weight"] for pair, ok
                       in zip(case["pairs"], pair_ok) if ok)
        assert total_u <= c_weight
        assert total_u_prime <= c_weight
        assert 2 * total_theta <= total_u + total_u_prime
        fractional_sum = sum(root for i, root in enumerate(case["roots"])
                             if labels[i] >= 0)
        assert (c_weight * target ** (e // 8) * size ** (4 ** k)
                >= size ** 3 * fractional_sum ** (4 ** k))
        f_weight = 0
        for config in case["configs"]:
            if config["mask"] & present != config["mask"]:
                continue
            if all((labels[a] + labels[d] - labels[b] - labels[c]) % target == 0
                   for a, b, c, d in config["faces"]):
                f_weight += config["weight"]
        weight_sum = sum(w for i, w in enumerate(case["weights"])
                         if labels[i] >= 0)
        configuration_eighth = 4 ** k - 3 ** k
        assert (f_weight * target ** configuration_eighth * size ** (4 ** k)
                >= size ** 3 * weight_sum ** (4 ** k))
    return admitted_count


def recurrence_checks():
    old = config = cube = 0
    table = []
    for k in range(1, 51):
        old = 4 * old + 8 * 4 ** (k - 1)
        config = 4 * config + 8 * 3 ** (k - 1)
        cube = 4 * cube + 8 * 2 ** (k - 1)
        assert old == 2 * k * 4 ** k
        assert config == 8 * (4 ** k - 3 ** k)
        assert cube == 4 * (4 ** k - 2 ** k)
        assert cube <= config <= old
        if k >= 2:
            assert cube < config < old
        for d in range(2, 21):
            arrangement = (3 * d - 2) * cube + 8 * (d - 1) * 2 ** k
            assert arrangement == (12 * d - 8) * 4 ** k - 4 * d * 2 ** k
            prior = (3 * d - 2) * old + 8 * (d - 1) * 2 ** k
            assert arrangement <= prior
        if k <= 5:
            table.append({"k": k, "original": old,
                          "configuration": config, "cube_pair": cube})

    gammas = [Fraction(1), Fraction(1, 2), Fraction(1, 3), Fraction(1, 5)]
    for base in (2, 3):
        coefficients = [8 * base ** i * 4 ** (3 - i) for i in range(4)]
        ordered_value = prod(g ** e for g, e in zip(gammas, coefficients))
        for permutation in itertools.permutations(gammas):
            assert prod(g ** e for g, e in zip(permutation, coefficients)) <= (
                ordered_value)
    return {"dimensions": 50, "arrangement_orders": [2, 20],
            "coordinate_order_checks": 48, "small_dimension_table": table}


def run():
    summaries = []
    # Exhaust all partial maps: -1 means absent, other values are target labels.
    for moduli, target in [((2, 2), 2), ((2, 2), 4), ((2, 3), 3)]:
        case = build_case(moduli, target)
        total_maps = (target + 1) ** case["size"]
        admitted = weighted_count = 0
        for number, labels in enumerate(itertools.product(
                range(-1, target), repeat=case["size"])):
            weighted = (number < 6 or number == total_maps - 1
                        or number % 97 == 0)
            admitted += verify_map(case, labels, weighted)
            weighted_count += int(weighted)
        summaries.append({
            "coordinate_orders": list(moduli), "target_cyclic_order": target,
            "exhaustive_partial_maps": total_maps,
            "ambient_gluing_parameters": len(case["records"]),
            "admitted_gluing_instances": admitted,
            "weighted_maps_checked_exactly": weighted_count,
            "two_orientation_maps": "both bijective on ambient parameters",
        })

    # Dimension three exercises repeated square-root induction.  The list
    # is deterministic and contains absent points, nonconstant labels,
    # characteristic two, and composite target torsion.
    for target in (2, 4):
        case = build_case((2, 2, 2), target)
        labels_list = [
            tuple(-1 for _ in range(8)),
            tuple(0 for _ in range(8)),
            tuple(i % target for i in range(8)),
            tuple((i * i + i // 2) % target for i in range(8)),
        ]
        labels_list += [
            tuple(-1 if (i + seed) % 5 == 0
                  else (i * (seed + 1) + i // 3) % target for i in range(8))
            for seed in range(24)
        ]
        admitted = sum(verify_map(case, labels, True) for labels in labels_list)
        summaries.append({
            "coordinate_orders": [2, 2, 2],
            "target_cyclic_order": target,
            "deterministic_partial_maps": len(labels_list),
            "ambient_gluing_parameters": len(case["records"]),
            "admitted_gluing_instances": admitted,
            "weighted_maps_checked_exactly": len(labels_list),
            "weights": "w_i=(i+1)^4; all calculations exact integers",
        })
    return {
        "status": "PASS",
        "method": "exact integer and rational arithmetic; no floating point",
        "scope": "finite audits support, and do not replace, the written proofs",
        "cases": summaries,
        "recurrences_and_ordering": recurrence_checks(),
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = run()
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text)
    print(text, end="")
