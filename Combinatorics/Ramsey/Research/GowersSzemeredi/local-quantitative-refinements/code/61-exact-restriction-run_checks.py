#!/usr/bin/env python3
"""Reproducible exact tests; computations are checks, not a proof assistant."""
from __future__ import annotations
from collections import Counter
from fractions import Fraction
from itertools import combinations, product
from pathlib import Path
import json
import random
import time
from exact_restriction import (
    AbelianGroup, avoidance_partition, bsg_core, ceil_log2, energy,
    freiman_partition, graph_of, is_freiman, multiple_sumset, sumset,
    verify_avoidance,
)


Gaussian = tuple[int, int]


def gaussian_energy(group: AbelianGroup, weights: dict, order: int) -> int:
    """An exact weighted convolution energy, with Gaussian-integer weights."""
    dist = {group.zero: (1, 0)}
    for _ in range(order):
        nxt = {}
        for x, (a, b) in dist.items():
            for y, (c, d) in weights.items():
                z = group.add(x, y)
                u, v = nxt.get(z, (0, 0))
                nxt[z] = (u + a*c - b*d, v + a*d + b*c)
        dist = nxt
    return sum(a*a + b*b for a, b in dist.values())


def run() -> dict:
    started = time.monotonic()
    result = {"arithmetic": "exact integers and fractions", "seed": 20261006,
              "proof_assistant_checked": False}
    for q in range(2, 10001):
        count = 2 * ((q + 4) // 5) - 1
        assert 2 * count <= q
    result["root_grid_orders_checked"] = 9999
    group_list = [(2,), (3,), (4,), (5,), (6,), (8,), (2, 2), (2, 4), (3, 3)]
    distributions = 0
    for mods in group_list:
        h = AbelianGroup(mods)
        for d in h.elements():
            if d == h.zero:
                continue
            hist = Counter(h.char_numerator(c, d) for c in h.elements())
            assert len(set(hist.values())) == 1
            assert 2 * sum(h.char_small(c, d) for c in h.elements()) <= h.order
            distributions += 1
    result["character_distributions_checked"] = distributions

    # Every forbidden set in each listed group, not only symmetric ones.
    partitions = 0
    for mods in [(2,), (3,), (4,), (5,), (6,), (8,), (2, 2), (2, 4)]:
        h = AbelianGroup(mods)
        nz = [x for x in h.elements() if x != h.zero]
        for mask in range(1 << len(nz)):
            forbidden = {x for i, x in enumerate(nz) if mask & (1 << i)}
            for m in (1, 2, 3, 8):
                chars, cells = avoidance_partition(h, forbidden, m)
                assert verify_avoidance(h, cells, forbidden, m)
                assert set().union(*cells) == set(h.elements())
                assert sum(map(len, cells)) == h.order
                partitions += 1
    result["exhaustive_avoidance_partitions_checked"] = partitions

    mappings = cases = bsg_cases = 0
    for gm, hm in [((2,), (2,)), ((3,), (3,)), ((4,), (4,)),
                   ((5,), (3,)), ((4,), (6,))]:
        g, h = AbelianGroup(gm), AbelianGroup(hm)
        xs, ys = g.elements(), h.elements()
        for values in product(ys, repeat=len(xs)):
            phi = dict(zip(xs, values))
            ambient, graph = graph_of(g, h, phi)
            n = len(graph)
            k = Fraction(len(sumset(ambient, graph, graph, True)), n)
            e2 = energy(ambient, graph, 2)
            for m in (2, 3, 8):
                chars, cells, defects = freiman_partition(g, h, phi, m)
                assert len(defects) <= k ** (2 * m + 1)
                assert len(chars) <= ceil_log2(len(defects))
                assert all(is_freiman(g, h, phi, c, m) for c in cells)
                assert sum(map(len, cells)) == n
                assert energy(ambient, graph, m) <= n ** (2 * m - 4) * e2
                for s in (2, m):
                    # Energy retention via the Fourier-norm triangle inequality.
                    lhs = sum(energy(g, c, s) for c in cells) * len(cells) ** (2*s-1)
                    assert lhs >= energy(g, phi, s)
                cases += 1
            if gm == (4,) and hm == (4,):
                core, cert = bsg_core(ambient, graph)
                core_phi = {z[:1]: z[1:] for z in core}
                _, cells, _ = freiman_partition(g, h, core_phi, 8)
                assert all(is_freiman(g, h, core_phi, c, 8) for c in cells)
                chosen = max(cells, key=len)
                actual_k = Fraction(len(sumset(ambient, core, core, True)), len(core))
                assert len(chosen) * len(cells) >= len(core)
                assert len(multiple_sumset(g, chosen, 8)) <= actual_k**8 * len(core)
                assert energy(g, chosen, 8) >= Fraction(len(core)**15, len(cells)**16) / actual_k**8
                bsg_cases += 1
            mappings += 1
    result["exhaustive_full_domain_maps_checked"] = mappings
    result["map_order_cases_checked"] = cases
    result["bsg_cores_checked"] = bsg_cases
    result["end_to_end_largest_cell_cases_checked"] = bsg_cases

    rng = random.Random(20261006)
    for _ in range(100):
        g, h = AbelianGroup((4, 2)), AbelianGroup((3, 4))
        xs = [x for x in g.elements() if rng.randrange(3) != 0]
        if not xs:
            xs = [g.zero]
        phi = {x: rng.choice(h.elements()) for x in xs}
        m = rng.choice((2, 3, 4, 8))
        _, cells, _ = freiman_partition(g, h, phi, m)
        assert all(is_freiman(g, h, phi, c, m) for c in cells)
    result["mixed_group_sampled_maps_checked"] = 100

    gaussian_cases = 0
    for _ in range(100):
        g, h = AbelianGroup((3, 2)), AbelianGroup((4,))
        phi = {x: rng.choice(h.elements()) for x in g.elements()}
        weights = {x: (rng.randint(-2, 2), rng.randint(-2, 2)) for x in phi}
        _, cells, _ = freiman_partition(g, h, phi, 3)
        ambient, _ = graph_of(g, h, phi)
        for order in (2, 3):
            cell_energy = 0
            for cell in cells:
                w = {x: weights[x] for x in cell}
                wg = {x + phi[x]: weights[x] for x in cell}
                value = gaussian_energy(g, w, order)
                assert value == gaussian_energy(ambient, wg, order)
                cell_energy += value
            assert cell_energy * len(cells)**(2*order - 1) >= gaussian_energy(g, weights, order)
            gaussian_cases += 1
    result["gaussian_integer_weight_cases_checked"] = gaussian_cases

    obstructions = []
    for e, r in [(2, 1), (2, 2), (3, 1), (3, 2), (4, 1)]:
        h = AbelianGroup((2 ** e,) * r)
        m = 2 ** (e - 1)
        torsion = {x for x in h.elements() if h.scale(2, x) == h.zero}
        forbidden = torsion - {h.zero}
        pair_count = 0
        for x, y in combinations(h.elements(), 2):
            d = h.sub(x, y)
            witnesses = [q for q in range(1, m + 1)
                         if h.scale(q, d) in forbidden]
            assert witnesses
            pair_count += 1
        _, cells = avoidance_partition(h, forbidden, m)
        assert len(cells) == h.order
        assert h.order == (len(forbidden) + 1) ** e
        # Canonical section graph: quotient modulo 2^(e-1).
        g = AbelianGroup((m,) * r)
        phi = {x: x for x in g.elements()}
        ambient, graph = graph_of(g, h, phi)
        assert len(sumset(ambient, graph, graph, True)) == (2 * m - 1) ** r
        expected_c = Fraction(2 * m * m + 1, 3 * m * m) ** r
        assert Fraction(energy(ambient, graph, 2), len(graph) ** 3) == expected_c
        for x, y in combinations(g.elements(), 2):
            assert not is_freiman(g, h, phi, {x, y}, m)
        obstructions.append({"e": e, "rank": r, "m": m,
                             "group_order": h.order, "forbidden_size": len(forbidden),
                             "certified_two_point_failures": pair_count,
                             "required_colors": h.order,
                             "section_graph_energy_density": str(expected_c)})
    result["torsion_obstructions"] = obstructions

    assert 40 ** 17 < 2 ** 91
    assert 9 + 24 * 91 == 2193
    assert 1 + 10 * 91 == 911
    assert 16 * 91 + 8 == 1464
    assert 96 + 45 + 24 * 1464 == 35277
    assert 15 + 10 * 1464 == 14655
    assert 35277 < 2 * 2 ** 19 and 14655 < 2 ** 19
    result["order_eight_constants"] = {
        "size": "2^(-2193) alpha^911 |B|",
        "energy": "2^(-35277) alpha^14655 |B|^15",
        "exact_comparisons": "passed",
    }
    result["all_assertions_passed"] = True
    result["elapsed_seconds"] = round(time.monotonic() - started, 3)
    return result


if __name__ == "__main__":
    results = run()
    target = Path(__file__).resolve().parents[1] / "checks" / "results.json"
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(results, indent=2) + "\n")
    print(json.dumps(results, indent=2))
