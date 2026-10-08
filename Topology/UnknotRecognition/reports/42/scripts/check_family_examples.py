#!/usr/bin/env python3
"""Replay the bundled cyclic-family examples and their arithmetic certificates.

Run from anywhere:
    python scripts/check_family_examples.py
    python scripts/check_family_examples.py --regenerate

The default reads stored artifacts.  --regenerate first rebuilds their inputs
and optimizer outputs from the formulas below, using only the bundled source.
Small cases use an independent literal sheet-orbit oracle.  The large case
checks binary arithmetic and hexadecimal JSON replay without expanding sheets.
"""

from __future__ import annotations

import argparse
from copy import deepcopy
from itertools import combinations, product
import json
from math import gcd
from pathlib import Path
import sys


sys.dont_write_bytecode = True
BUNDLE = Path(__file__).resolve().parents[1]
FAST_SOURCE = BUNDLE / "source" / "Topology" / "UnknotRecognition" / "fast"
EXAMPLES = BUNDLE / "examples" / "cyclic_families"
sys.path.insert(0, str(FAST_SOURCE))

from fastunknot.cyclic_cover_family import (
    compile_family,
    component_count_at,
    optimize_cover_family,
    realize_family,
    verify_cover_family_certificate,
)
from fastunknot.integer_codec import encoded_integer, json_safe


def expression(constant=0, coefficients=()):
    return {"constant": constant, "coefficients": list(coefficients)}


def annulus(modulus, monodromy, *, phase_constant=0, direction=-1):
    return {
        "sheets": modulus,
        "variables": 1,
        "pieces": [{
            "surface": {"orientable": True, "genus": 0, "boundary_components": 2},
            "monodromy": [expression(monodromy, [0])],
        }],
        "seams": [{
            "left": [0, 0], "right": [0, 1], "direction": direction,
            "shift": expression(phase_constant, [1]),
        }],
        "constraints": {"matrix": [], "rhs": []},
    }


def specifications():
    constrained = annulus(12, 6)
    constrained["constraints"] = {"matrix": [[2]], "rhs": [8]}
    large_modulus = 6 ** 4096
    edges = list(combinations(range(4), 2))
    k4 = {
        "sheets": 3,
        "variables": 4,
        "pieces": [{
            "surface": {"orientable": True, "genus": 0, "boundary_components": 7},
            "monodromy": [expression(0, [int(i == u) - int(i == v) for i in range(4)])
                          for u, v in edges],
        }],
        "seams": [],
        "constraints": {"matrix": [], "rhs": []},
    }
    return [
        {
            "name": "constrained_annulus12", "literal": True,
            "input": constrained,
            "expected": {"feasible": True, "minimum_components": 2,
                         "solution_count": 2, "feasible_parameters": [[4], [10]]},
        },
        {
            "name": "disconnected_annuli_to_connected", "literal": True,
            "input": annulus(12, 0),
            "expected": {"feasible": True, "minimum_components": 1,
                         "solution_count": 12, "local_component_count": 12},
        },
        {
            "name": "infeasible_annulus", "literal": True,
            "input": annulus(7, 1, direction=1),
            "expected": {"feasible": False, "solution_count": 0},
        },
        {
            "name": "large_hex_roundtrip", "literal": False,
            "input": annulus(hex(large_modulus), 0, phase_constant=2),
            "expected": {"feasible": True, "minimum_components": 1,
                         "modulus_formula": "6^4096", "modulus_bits": large_modulus.bit_length(),
                         "witness_formula": "3^4096", "expanded_sheet_records": 0},
        },
        {
            "name": "k4_global_family", "literal": True,
            "input": k4,
            "expected": {"feasible": True, "minimum_components": 1,
                         "solution_count": 81, "globally_connected_assignments": 78},
        },
    ]


def designated_boundary_metadata():
    return {
        "family_input": "k4_global_family.input.json",
        "graph": "K4",
        "vertices": [0, 1, 2, 3],
        "edges": [list(edge) for edge in combinations(range(4), 2)],
        "piece": 0,
        "designated_boundaries": [0, 1, 2, 3, 4, 5],
        "required_components_per_preimage": 1,
        "expected": {"assignments_examined": 81, "globally_connected_assignments": 78,
                     "all_designated_preimages_connected_assignments": 0},
        "reason": "The six designated boundary translations are all pairwise differences of four residues modulo 3. Four residues cannot be pairwise distinct.",
        "scope": "This metadata describes an additional peripheral query. It is not part of the strict cyclic-family input schema or an optimizer feasibility claim.",
    }


def write_json(path, value):
    path.write_text(json.dumps(json_safe(value), indent=2) + "\n", encoding="utf-8")


def expected_manifest(specs):
    return {
        "schema": "cyclic-family-example-manifest-v1",
        "source": "source/Topology/UnknotRecognition/fast",
        "examples": [{
            "name": spec["name"], "input": spec["name"] + ".input.json",
            "output": spec["name"] + ".output.json", "literal_check": spec["literal"],
            "expected": spec["expected"],
        } for spec in specs],
        "peripheral_metadata": "k4.designated_boundaries.json",
    }


def regenerate(specs):
    EXAMPLES.mkdir(parents=True, exist_ok=True)
    for spec in specs:
        write_json(EXAMPLES / (spec["name"] + ".input.json"), spec["input"])
        write_json(EXAMPLES / (spec["name"] + ".output.json"),
                   optimize_cover_family(spec["input"]))
    write_json(EXAMPLES / "manifest.json", expected_manifest(specs))
    write_json(EXAMPLES / "k4.designated_boundaries.json", designated_boundary_metadata())


def value(expr, parameters, modulus):
    return (encoded_integer(expr["constant"]) + sum(encoded_integer(a) * b
            for a, b in zip(expr["coefficients"], parameters))) % modulus


def literal_components(raw, parameters):
    """Independent DSU on piece x sheet for these small planar examples.

    This oracle has no spanning tree, compiled holonomies, affine solver,
    or component gcd formula.  Planar peripheral words are formed directly.
    """
    modulus = encoded_integer(raw["sheets"])
    if modulus > 100:
        raise ValueError("literal expansion is restricted to the small examples")
    for row, rhs in zip(raw["constraints"]["matrix"], raw["constraints"]["rhs"]):
        if (sum(encoded_integer(a) * z for a, z in zip(row, parameters))
                - encoded_integer(rhs)) % modulus:
            return None
    parent = list(range(modulus * len(raw["pieces"])))
    def root(index):
        while parent[index] != index:
            parent[index] = parent[parent[index]]
            index = parent[index]
        return index
    def join(left, right):
        parent[root(left)] = root(right)
    peripheral = []
    for index, piece in enumerate(raw["pieces"]):
        surface = piece["surface"]
        if surface["orientable"] is not True or encoded_integer(surface["genus"]) != 0:
            raise ValueError("this literal example oracle expects planar patches")
        shifts = [value(expr, parameters, modulus) for expr in piece["monodromy"]]
        assert len(shifts) + 1 == encoded_integer(surface["boundary_components"])
        peripheral.append(shifts + [-sum(shifts) % modulus])
        for shift in shifts:
            for sheet in range(modulus):
                join(index * modulus + sheet,
                     index * modulus + (sheet + shift) % modulus)
    for seam in raw["seams"]:
        u, ub = seam["left"]
        v, vb = seam["right"]
        direction = encoded_integer(seam["direction"])
        if (peripheral[u][ub] - direction * peripheral[v][vb]) % modulus:
            return None
        shift = value(seam["shift"], parameters, modulus)
        for sheet in range(modulus):
            join(u * modulus + sheet, v * modulus + (sheet + shift) % modulus)
    return len({root(index) for index in range(len(parent))})


def permutation_cycle_count(shift, modulus):
    remaining = set(range(modulus))
    cycles = 0
    while remaining:
        cycles += 1
        start = min(remaining)
        current = start
        while current in remaining:
            remaining.remove(current)
            current = (current + shift) % modulus
    return cycles


def check_k4_boundaries(raw):
    metadata = json.loads((EXAMPLES / "k4.designated_boundaries.json").read_text())
    assert metadata == designated_boundary_metadata()
    selected_count = global_count = assignments = 0
    for parameters in product(range(3), repeat=4):
        assignments += 1
        shifts = [value(expr, parameters, 3) for expr in raw["pieces"][0]["monodromy"]]
        assert shifts == [(parameters[u] - parameters[v]) % 3 for u, v in metadata["edges"]]
        boundary_counts = [permutation_cycle_count(shift, 3) for shift in shifts]
        prescribed_connected = all(boundary_counts[index] == 1
                                   for index in metadata["designated_boundaries"])
        proper_colouring = all(parameters[u] != parameters[v] for u, v in metadata["edges"])
        assert prescribed_connected == proper_colouring
        selected_count += prescribed_connected
        global_count += literal_components(raw, parameters) == 1
    assert assignments == 81 and global_count == 78 and selected_count == 0
    return {"assignments_examined": assignments, "globally_connected_assignments": global_count,
            "all_designated_preimages_connected_assignments": selected_count}


def check_examples(specs):
    manifest = json.loads((EXAMPLES / "manifest.json").read_text())
    assert manifest == expected_manifest(specs)
    records = []
    for spec in specs:
        raw = json.loads((EXAMPLES / (spec["name"] + ".input.json")).read_text())
        proposed = json.loads((EXAMPLES / (spec["name"] + ".output.json")).read_text())
        assert raw == json_safe(spec["input"]), spec["name"]
        # Fresh compilation validates the original input, never the stored
        # producer compilation.  The verifier recompiles once more itself.
        compile_family(raw)
        assert verify_cover_family_certificate(raw, proposed), spec["name"]
        assert verify_cover_family_certificate(raw, json.loads(json.dumps(proposed)))
        optimization = proposed["optimization"]
        expected = spec["expected"]
        assert optimization["feasible"] is expected["feasible"]
        record = {"example": spec["name"], "certificate_valid": True,
                  "feasible": optimization["feasible"]}
        if optimization["feasible"]:
            minimum = encoded_integer(optimization["minimum_components"])
            parameters = [encoded_integer(x) for x in optimization["parameters"]]
            assert minimum == expected["minimum_components"]
            assert component_count_at(raw, parameters) == minimum
            realize_family(raw, parameters)
            record["minimum_components"] = minimum
        if spec["literal"]:
            modulus = encoded_integer(raw["sheets"])
            assignments = list(product(range(modulus), repeat=raw["variables"]))
            feasible = [(list(point), count) for point in assignments
                        if (count := literal_components(raw, point)) is not None]
            assert len(feasible) == encoded_integer(optimization["solution_count"])
            assert len(feasible) == expected["solution_count"]
            if feasible:
                assert min(count for _, count in feasible) == minimum
                for point, count in feasible:
                    assert component_count_at(raw, point) == count
            if "feasible_parameters" in expected:
                assert [point for point, _ in feasible] == expected["feasible_parameters"]
            record.update(assignments_examined=len(assignments),
                          feasible_assignments=len(feasible))
            if spec["name"] == "disconnected_annuli_to_connected":
                local = deepcopy(raw)
                local["seams"] = []
                assert literal_components(local, [0]) == expected["local_component_count"]
                record["local_component_count"] = expected["local_component_count"]
            if spec["name"] == "k4_global_family":
                record["peripheral_query"] = check_k4_boundaries(raw)
        else:
            modulus = encoded_integer(raw["sheets"])
            assert modulus == 6 ** 4096 and modulus.bit_length() <= 20000
            assert encoded_integer(optimization["solution_count"]) == modulus
            assert parameters == [3 ** 4096]
            assert isinstance(optimization["parameters"][0], str)
            assert gcd(modulus, 2 + parameters[0]) == 1
            record.update(modulus_bits=modulus.bit_length(),
                          hexadecimal_witness_roundtrip=True, expanded_sheet_records=0)
        records.append(record)
    return {"status": "passed", "source": str(FAST_SOURCE.relative_to(BUNDLE)),
            "examples_checked": len(records), "records": records}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--regenerate", action="store_true",
                        help="rebuild the supplied input and certificate artifacts before checking")
    parser.add_argument("--report", type=Path, help="optional path for the JSON check report")
    options = parser.parse_args()
    specs = specifications()
    if options.regenerate:
        regenerate(specs)
    result = check_examples(specs)
    if options.report:
        write_json(options.report, result)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
