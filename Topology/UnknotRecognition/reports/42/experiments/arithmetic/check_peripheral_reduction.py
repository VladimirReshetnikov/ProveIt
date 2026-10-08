"""Check the colouring reduction against the maintained surface-cover kernel.

Example:
python agent_family/check_peripheral_reduction.py \
  --fast-root ProveIt/Topology/UnknotRecognition/fast \
  --output agent_family/peripheral_reduction_checks.json
"""

import argparse
from itertools import combinations, product
import json
from math import gcd
from pathlib import Path
import sys


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--fast-root", required=True)
    parser.add_argument("--output", default="peripheral_reduction_checks.json")
    options = parser.parse_args()
    sys.path.insert(0, str(Path(options.fast_root).resolve()))
    from fastunknot.surface_cover import classify_cover

    cases = [
        ("K3", 3, list(combinations(range(3), 2)), 6),
        ("K4", 4, list(combinations(range(4), 2)), 0),
        ("C5", 5, [(index, (index + 1) % 5) for index in range(5)], 30),
    ]
    records = []
    for name, vertices, edges, expected_colourings in cases:
        proper_count = 0
        peripheral_count = 0
        globally_connected_count = 0
        for colours in product(range(3), repeat=vertices):
            shifts = [(colours[u] - colours[v]) % 3 for u, v in edges]
            classified = classify_cover({
                "surface": {"orientable": True, "genus": 0,
                            "boundary_components": len(edges) + 1},
                "sheets": 3,
                "monodromy": [{"sign": 1, "shift": value} for value in shifts],
            })
            assert classified["component_count"] == gcd(3, *shifts)
            assert classified["boundary_monodromy"][-1]["shift"] == -sum(shifts) % 3
            lifted_boundary_counts = [
                sum(family["multiplicity"] * sum(record["multiplicity"]
                                                for record in family["boundary_lifts"][index])
                    for family in classified["families"])
                for index in range(len(edges))
            ]
            assert lifted_boundary_counts == [gcd(3, value) for value in shifts]
            proper = all(colours[u] != colours[v] for u, v in edges)
            prescribed_connected = all(value == 1 for value in lifted_boundary_counts)
            assert proper == prescribed_connected
            proper_count += proper
            peripheral_count += prescribed_connected
            globally_connected_count += classified["component_count"] == 1
        assert proper_count == expected_colourings
        records.append({
            "graph": name, "vertices": vertices, "edges": len(edges),
            "assignments_checked": 3 ** vertices,
            "proper_three_colourings": proper_count,
            "prescribed_boundary_connected_assignments": peripheral_count,
            "globally_connected_assignments": globally_connected_count,
        })
    with open(options.output, "w", encoding="utf-8") as handle:
        json.dump({"date": "2026-10-08", "records": records}, handle, indent=2)
        handle.write("\n")
    print(json.dumps(records, indent=2))


if __name__ == "__main__":
    main()
