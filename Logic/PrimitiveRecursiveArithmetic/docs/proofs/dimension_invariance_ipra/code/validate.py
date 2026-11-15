#!/usr/bin/env python3
"""Reproducible finite audits; these tests are not a formal iPRA proof.

Checks the independent certificate checker, rational cell boundaries, Kuhn
facet incidence, Sperner parity, exhaustive small colourings/maps, and larger
deterministic random rational tables.  Writes validation.json alongside this
script unless an output path is given.
"""

from __future__ import annotations

import argparse
import copy
import json
import random
from collections import Counter
from fractions import Fraction
from itertools import combinations, product
from pathlib import Path

from finite_dimension import (
    EXAMPLE, Instance, cell_of, extract, grid_points, kuhn_simplices,
    rational, staggered_data, verify_certificate,
)


def admissible_colours(v, d, N):
    return [colour for colour in range(d + 1)
            if all((v[i] != 0 or colour <= i)
                   and (v[i] != N or colour != i) for i in range(d))]


def fully_labelled_count(d, N, labels):
    return sum({labels[v] for v in vertices} == set(range(d + 1))
               for _, _, vertices in kuhn_simplices(d, N))


def parity_audit(d, N, labels):
    """Reconstruct incidence from vertex sets, independently of facet pairing."""
    assert all(labels[v] in admissible_colours(v, d, N) for v in labels)
    if d == 0:
        assert fully_labelled_count(d, N, labels) == 1
        return 1
    facets = Counter()
    special_occurrences = 0
    full_count = 0
    wanted = set(range(d))
    for _, _, vertices in kuhn_simplices(d, N):
        colours = [labels[v] for v in vertices]
        full = set(colours) == set(range(d + 1))
        full_count += full
        special_here = 0
        for deleted in range(d + 1):
            facet = tuple(sorted(vertices[:deleted] + vertices[deleted + 1:]))
            facets[facet] += 1
            special_here += {labels[v] for v in facet} == wanted
        assert special_here in (0, 1, 2)
        assert special_here % 2 == int(full)
        special_occurrences += special_here

    boundary_special = 0
    for facet, multiplicity in facets.items():
        assert multiplicity in (1, 2)
        boundary_axes = [(i, side) for i in range(d) for side in (0, N)
                         if all(v[i] == side for v in facet)]
        assert (multiplicity == 1) == bool(boundary_axes)
        if multiplicity == 1 and {labels[v] for v in facet} == wanted:
            boundary_special += 1
            assert all(v[d - 1] == 0 for v in facet)

    restricted = {v: labels[v + (0,)] for v in grid_points(d - 1, N)}
    lower_count = fully_labelled_count(d - 1, N, restricted)
    assert boundary_special == lower_count
    assert special_occurrences % 2 == boundary_special % 2 == full_count % 2 == 1
    parity_audit(d - 1, N, restricted)
    return full_count


def instance_from_rows(d, m, N, rows, delta=Fraction(1)):
    return Instance.from_json({"d": d, "m": m, "N": N,
                               "delta": str(delta),
                               "table": [[str(x) for x in row] for row in rows]})


def run():
    rng = random.Random(20261115)
    report = {
        "status": "passed", "random_seed": 20261115,
        "arithmetic": "fractions.Fraction; no floating-point coordinates",
        "scope": "finite executable audits, not a Lean proof or an iPRA proof certificate",
        "tests": {},
    }

    # Negative values and points exactly at, below and above cell boundaries.
    boundary_cases = 0
    for d in range(1, 8):
        for i in range(d):
            for k in range(-4, 5):
                delta = Fraction(3, 7)
                threshold = delta * (k + Fraction(i, d))
                small = delta / (10 * d)
                assert cell_of((threshold,), i, d, delta) == (k,)
                assert cell_of((threshold - small,), i, d, delta) == (k - 1,)
                assert cell_of((threshold + small,), i, d, delta) == (k,)
                boundary_cases += 3
    report["tests"]["exact_cell_boundary_cases"] = boundary_cases

    lattice_cases = 0
    for d in range(2, 9):
        for i, j in combinations(range(d), 2):
            for k, ell in product(range(-3, 4), repeat=2):
                gap = abs((Fraction(k) + Fraction(i, d))
                          - (Fraction(ell) + Fraction(j, d)))
                assert gap >= Fraction(1, d)
                lattice_cases += 1
    report["tests"]["staggered_lattice_separation_cases"] = lattice_cases

    # Exhaust all admissible label tables for these finite cubes.
    colourings = 0
    colouring_parameters = [(0, 1), (1, 1), (1, 2), (1, 4),
                           (2, 1), (2, 2), (2, 3), (3, 1), (4, 1)]
    for d, N in colouring_parameters:
        vertices = list(grid_points(d, N))
        options = [admissible_colours(v, d, N) for v in vertices]
        for values in product(*options):
            labels = dict(zip(vertices, values))
            parity_audit(d, N, labels)
            colourings += 1
    report["tests"]["exhaustive_admissible_colourings"] = colourings
    report["tests"]["colouring_parameters_d_N"] = colouring_parameters

    random_colourings = 0
    for d, N, repetitions in [(3, 2, 100), (3, 3, 30), (4, 2, 20), (5, 1, 10)]:
        for _ in range(repetitions):
            labels = {v: rng.choice(admissible_colours(v, d, N))
                      for v in grid_points(d, N)}
            parity_audit(d, N, labels)
            random_colourings += 1
    report["tests"]["random_admissible_colourings"] = random_colourings

    kinds = Counter()
    map_count = 0
    # Exhaust all 5^4 rational maps on a square's four vertices into a line.
    for values in product(range(-2, 3), repeat=4):
        instance = instance_from_rows(2, 1, 1, [(Fraction(v, 3),) for v in values],
                                      Fraction(1, 3))
        certificate = extract(instance)
        assert verify_certificate(instance, certificate)
        kinds[certificate["kind"]] += 1
        map_count += 1
    report["tests"]["exhaustive_rational_tables"] = map_count
    report["tests"]["exhaustive_table_outcomes"] = dict(kinds)

    random_kinds = Counter()
    random_maps = 0
    # Unique first coordinates force the second branch and exercise its proof.
    for d, m, N in [(2, 1, 2), (3, 1, 2), (3, 2, 2), (4, 2, 1),
                    (4, 3, 2), (5, 4, 1)]:
        count = (N + 1) ** d
        for _ in range(12):
            unique = list(range(count))
            rng.shuffle(unique)
            rows = [(Fraction(unique[t] - count // 2, 7),)
                    + tuple(Fraction(rng.randrange(-30, 31), 11) for _ in range(m - 1))
                    for t in range(count)]
            instance = instance_from_rows(d, m, N, rows, Fraction(1, 7))
            certificate = extract(instance)
            assert certificate["kind"] == "simplex_variation"
            assert verify_certificate(instance, certificate)
            _, _, labels = staggered_data(instance)
            parity_audit(d, N, labels)
            random_kinds[certificate["kind"]] += 1
            random_maps += 1
    for d, m, N in [(2, 1, 2), (3, 2, 2), (4, 1, 1)]:
        for _ in range(20):
            rows = [tuple(Fraction(rng.randrange(-5, 6), 7) for _ in range(m))
                    for _ in grid_points(d, N)]
            instance = instance_from_rows(d, m, N, rows, Fraction(1, 7))
            certificate = extract(instance)
            assert verify_certificate(instance, certificate)
            random_kinds[certificate["kind"]] += 1
            random_maps += 1
    report["tests"]["random_rational_tables"] = random_maps
    report["tests"]["random_table_outcomes"] = dict(random_kinds)

    # Dimensions zero are handled without fictitious target coordinates.
    zero_target_cases = 0
    for d in range(1, 5):
        for N in (1, 2):
            instance = instance_from_rows(d, 0, N, [() for _ in grid_points(d, N)])
            certificate = extract(instance)
            assert certificate["kind"] == "opposite_face_failure"
            assert rational(certificate["distance"]) == 0
            assert verify_certificate(instance, certificate)
            zero_target_cases += 1
    report["tests"]["zero_target_dimension_cases"] = zero_target_cases

    rejected = 0
    for data in [
        {"d": 0, "m": 0, "N": 1, "delta": "1", "table": [[]]},
        {"d": 1, "m": 1, "N": 1, "delta": "1", "table": [[0], [1]]},
    ]:
        try:
            extract(Instance.from_json(data))
        except ValueError:
            rejected += 1
        else:
            raise AssertionError("d<=m must not assert a dimensional obstruction")
    for changes in [dict(N=0), dict(delta="0"), dict(delta="-1"),
                    dict(table=[[0.0], [1], [2], [3]])]:
        data = dict(EXAMPLE)
        data.update(changes)
        try:
            Instance.from_json(data)
        except ValueError:
            rejected += 1
        else:
            raise AssertionError("malformed or inexact input was accepted")
    report["tests"]["invalid_or_inapplicable_inputs_rejected"] = rejected

    # Deliberately corrupt final witnesses; checker must reject each one.
    instance = Instance.from_json(EXAMPLE)
    certificate = extract(instance)
    assert certificate["kind"] == "simplex_variation"
    bad_certificates = []
    bad = copy.deepcopy(certificate)
    bad["v"] = bad["u"]
    bad_certificates.append(bad)
    bad = copy.deepcopy(certificate)
    bad["base"] = [9, 9]
    bad_certificates.append(bad)
    bad = copy.deepcopy(certificate)
    bad["permutation"] = [0, 0]
    bad_certificates.append(bad)
    bad = copy.deepcopy(certificate)
    bad["u"][0] = float(bad["u"][0])
    bad_certificates.append(bad)
    bad = copy.deepcopy(certificate)
    bad["permutation"] = [False, True]
    bad_certificates.append(bad)
    bad_certificates.append({"kind": "opposite_face_failure", "source_axis": 0,
                             "u": [0, 0], "v": [1, 0]})
    bad_certificates.append({"kind": "opposite_face_failure", "source_axis": 1,
                             "u": [0, 0], "v": [0, 0]})
    for bad in bad_certificates:
        assert not verify_certificate(instance, bad)
    report["tests"]["invalid_certificates_rejected"] = len(bad_certificates)
    report["example_input"] = EXAMPLE
    report["example_certificate"] = certificate
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("validation.json"))
    args = parser.parse_args()
    report = run()
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": report["status"], "tests": report["tests"],
                      "output": str(args.output.resolve())}, indent=2))


if __name__ == "__main__":
    main()
