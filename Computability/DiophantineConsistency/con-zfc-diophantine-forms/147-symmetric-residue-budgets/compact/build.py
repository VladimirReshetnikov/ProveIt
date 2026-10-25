#!/usr/bin/env python3
"""Emit the two equations obtained by deleting the auxiliary alpha shift."""
from __future__ import annotations
import argparse
from collections import Counter
from copy import deepcopy
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def build(parent_file: str, new_file: str, expected_ops: int, check: bool):
    parent = json.loads((ROOT / "upstream" / parent_file).read_text())
    data = deepcopy(parent)
    rows = []
    for name, op, left, right in parent["source"]:
        if name == "Tp":
            if [op, left, right] != ["+", "T", "alpha"]:
                raise ValueError("Unexpected parent auxiliary shift")
            continue
        rows.append([name, op, "T" if left == "Tp" else left,
                     "T" if right == "Tp" else right])
    data["source"] = rows
    data["name"] = "unshifted_auxiliary_" + parent["transport_weight"]
    data["operations"] = len(rows)
    if len(rows) != expected_ops:
        raise ValueError("Unexpected operation count")
    data["operation_breakdown"] = dict(sorted(Counter(row[1] for row in rows).items()))
    data["coefficient_binding"]["path"] = "upstream/coefficients/"
    data["parent"] = "upstream/" + parent_file
    data["proof"] = "PROOF.md"
    data["exact_identity"] = "P_new(T) = P_parent(T-alpha)"
    data["zero_set_bijection"] = "T_new=T_parent+alpha; T_parent=T_new-alpha"
    encoded = json.dumps(data, indent=2, ensure_ascii=False) + "\n"
    target = ROOT / new_file
    if check:
        if target.read_text() != encoded:
            raise ValueError("Rebuild differs: " + new_file)
    else:
        target.write_text(encoded)
    return {"file": new_file, "operations": len(rows), "degree": data["exact_degree"]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = [build("equation78.json", "equation77_degree630.json", 77, args.check),
              build("equation79.json", "equation78_degree468.json", 78, args.check)]
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
