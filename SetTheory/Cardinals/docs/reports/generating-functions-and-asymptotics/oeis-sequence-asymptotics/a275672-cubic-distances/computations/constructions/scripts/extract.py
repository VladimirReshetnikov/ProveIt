#!/usr/bin/env python3
"""Extract a maximum valid subset of a supplied small approximate configuration.

This optimizes only over the supplied points; no global maximality is implied.
"""
import argparse
import itertools
import json
from pathlib import Path
from verify import verify


def extract(record):
    points = record["points"]
    edges_by_distance = {}
    for i, j in itertools.combinations(range(len(points)), 2):
        distance = sum((a-b)**2 for a, b in zip(points[i], points[j]))
        edges_by_distance.setdefault(distance, []).append({i, j})
    forbidden = []
    for edges in edges_by_distance.values():
        for e, f in itertools.combinations(edges, 2):
            forbidden.append(e | f)
    vertices = range(len(points))
    for r in range(len(points)+1):
        for removed_tuple in itertools.combinations(vertices, r):
            removed = set(removed_tuple)
            if all(removed & constraint for constraint in forbidden):
                result = {
                    "n": record["n"],
                    "k": len(points)-r,
                    "points": [p for i,p in enumerate(points) if i not in removed],
                    "collision_pairs": 0,
                    "algorithm": "minimum vertex deletion from approximate configuration",
                    "removed_point_indices": list(removed_tuple),
                }
                verify(result)
                return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    result = extract(json.loads(args.input.read_text()))
    result["source_file"] = args.input.name
    args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(f"Verified n={result['n']} lower bound k={result['k']}")


if __name__ == "__main__":
    main()
