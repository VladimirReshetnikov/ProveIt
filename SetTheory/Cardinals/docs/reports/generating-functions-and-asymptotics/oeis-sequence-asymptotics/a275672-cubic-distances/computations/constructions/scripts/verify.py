#!/usr/bin/env python3
"""Verify a finite unique-distance certificate using only integer arithmetic.

Usage: python verify.py input.json [input2.json ...]
       python verify.py --collect witness_certificates.json

An explicit input must be a valid witness. --collect collects only files that
claim collision_pairs=0; all such claims are independently checked. Invalid
approximate search outputs are never reported as lower bounds.
"""
import argparse
import hashlib
import itertools
import json
from pathlib import Path


def verify(record):
    n, k, points = record["n"], record["k"], record["points"]
    assert type(n) is int and n >= 1
    assert type(k) is int and k == len(points)
    assert all(len(p) == 3 for p in points)
    assert all(type(c) is int and 0 <= c < n for p in points for c in p)
    assert len({tuple(p) for p in points}) == k, "Repeated point"
    distance_pairs = {}
    for (i, p), (j, q) in itertools.combinations(enumerate(points), 2):
        distance = sum((a-b)**2 for a, b in zip(p, q))
        assert distance > 0
        assert distance not in distance_pairs, (
            f"Repeated squared distance {distance}: "
            f"{distance_pairs.get(distance)} and {[i,j]}"
        )
        distance_pairs[distance] = [i, j]
    assert len(distance_pairs) == k*(k-1)//2
    result = dict(record)
    result.update(
        verified=True,
        unordered_pair_count=k*(k-1)//2,
        squared_distances=sorted(distance_pairs),
        distance_to_point_indices={str(d): distance_pairs[d]
                                   for d in sorted(distance_pairs)},
    )
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("inputs", nargs="*", type=Path)
    parser.add_argument("--collect", type=Path)
    args = parser.parse_args()
    paths = args.inputs
    if args.collect:
        paths = [p for p in sorted(Path(__file__).parent.glob("*.json"))
                 if p.resolve() != args.collect.resolve()]
    certificates = []
    for path in paths:
        record = json.loads(path.read_text())
        if not isinstance(record, dict) or "collision_pairs" not in record:
            if args.collect:
                continue
            raise ValueError(f"Unexpected record: {path}")
        if args.collect and record["collision_pairs"] != 0:
            continue
        checked = verify(record)
        checked["source_file"] = path.name
        checked["source_sha256"] = hashlib.sha256(path.read_bytes()).hexdigest()
        certificates.append(checked)
        print(f"{path.name}: n={checked['n']}, k={checked['k']}, "
              f"{checked['unordered_pair_count']} distinct positive squared distances: PASS")
    if args.collect:
        args.collect.write_text(json.dumps({
            "description": "Independently checked constructive lower bounds; no maximality claim",
            "coordinates": "Integers from 0 through n-1 in each coordinate",
            "certificates": certificates,
        }, indent=2)+"\n")


if __name__ == "__main__":
    main()
