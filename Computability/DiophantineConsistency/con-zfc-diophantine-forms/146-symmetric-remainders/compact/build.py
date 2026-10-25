#!/usr/bin/env python3
"""Build three exact circuits with the existing XY carrier denominator.

The only external inputs are the two frozen parent JSON equations.  No
parent program is imported.  The transformation is an explicit row rewrite.
"""
from __future__ import annotations
import argparse
from collections import Counter
from copy import deepcopy
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def compile_variant(parent, parent_name, weight, carrier):
    expected = {
        "Xp1": ["Xp1", "+", "X", 1],
        "Am1": ["Am1", "*", "Y", "Xp1"],
        "Y2": ["Y2", "*", "Y", "Y"],
        "V0": ["V0", "*", "X", "Y2"],
    }
    rows = []
    seen = set()
    for row in parent["source"]:
        name, op, left, right = row
        if name in expected:
            if row != expected[name]:
                raise ValueError("Parent changed at " + name)
            seen.add(name)
        if name == "Xp1":
            rows.append(["D" if carrier == "XY" else "XY", "*", "X", "Y"])
        elif name == "Am1":
            rows.append(["Am1", "+", "D" if carrier == "XY" else "XY", "Y"])
        elif name == "Y2":
            if carrier == "q4":
                rows.append(["D", "*", "q2", "q2"])
        elif name == "V0":
            rows.append(["V0", "*", "D" if carrier == "XY" else "XY", "Y"])
        else:
            rows.append([name, op, "D" if left == "Y2" else left,
                         "D" if right == "Y2" else right])
    if seen != set(expected):
        raise ValueError("Incomplete parent pattern")
    data = deepcopy(parent)
    data.update({
        "name": carrier.lower() + "_carrier_" + weight,
        "source": rows,
        "operations": len(rows),
        "operation_breakdown": dict(sorted(Counter(r[1] for r in rows).items())),
        "exact_degree": 626 if weight == "V2" else 464 if carrier == "XY" else 460,
        "carrier_denominator": "D=X*Y" if carrier == "XY" else "D=q^4",
        "proof": "PROOF.md",
        "parent": "parent/" + parent_name,
    })
    return data


def encode(data):
    return json.dumps(data, indent=2, ensure_ascii=False) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = []
    for source, target, weight, carrier in [("equation78.json", "equation77.json", "V2", "XY"),
                                           ("equation79.json", "equation78.json", "bV", "XY"),
                                           ("equation79.json", "equation79.json", "bV", "q4")]:
        parent = json.loads((ROOT / "parent" / source).read_text())
        data = encode(compile_variant(parent, source, weight, carrier))
        path = ROOT / target
        if args.check:
            if path.read_text() != data:
                raise ValueError("Rebuild differs: " + target)
        else:
            path.write_text(data)
        result.append({"path": target, "bytes": len(data.encode()),
                       "status": "verified" if args.check else "created"})
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
