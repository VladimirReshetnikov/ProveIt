#!/usr/bin/env python3
"""Rebuild the two equal-weight circuits from pinned complete source circuits.

This only removes one multiplication. Semantic equisolvability is proved in
PROOF.md; it is not inferred from finite evaluation checks.
"""
import argparse
import copy
import hashlib
import json
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent
PIN = "84e16e43092614bae262ca59651cb9d77e31a255"


def require(value, label):
    if not value:
        raise AssertionError(label)


def render(value):
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def make(source_name, count, exact_degree, auxiliary_gap=False):
    raw = (ROOT / "source" / source_name).read_bytes()
    parent = json.loads(raw)
    rows = parent["source"]
    require(["Dtau9", "*", 9, "Dtau"] in rows, "parent multiplier")
    require(["fa", "*", "dM2", "Dtau9"] in rows, "parent multiplier consumer")
    require(sum(str(row).count("Dtau9") for row in rows) == 2, "exclusive multiplier use")
    output = copy.deepcopy(parent)
    output["source"] = [
        ["fa", "*", "dM2", "Dtau"] if row[0] == "fa" else row
        for row in rows if row[0] != "Dtau9"
    ]
    if auxiliary_gap:
        require(["HI", "*", "Hp", "I"] in output["source"], "old HI majorant row")
        require(["L", "+", "HI", "cTR"] in output["source"], "old L majorant row")
        output["source"] = [
            [row[0], row[1], row[2], "cTR"] if row[0] == "qm1L" else row
            for row in output["source"] if row[0] not in ("HI", "L")
        ]
    label = "auxiliary_gap" if auxiliary_gap else "equal_weight"
    output["name"] = f"ten_positive_{label}_{count}_degree{exact_degree}"
    output["exact_degree"] = exact_degree
    output["operations"] = count
    output["operation_breakdown"] = dict(Counter(row[1] for row in output["source"]))
    output["source_pin"] = PIN
    output["parent_sha256"] = hashlib.sha256(raw).hexdigest()
    output["parent_local_file"] = "source/" + source_name
    output["proof"] = "PROOF.md"
    output["proof_status"] = (
        "Ordinary positive-zero existence equivalence by equal-weight radical "
        "separation, the proved auxiliary-index gap when enabled, and the "
        "retained complete zero-offset source proof. "
        "No new Lean or internal-ZFC formalization."
    )
    output["polynomial_relation"] = (
        "Different polynomial; positive solvability is equivalent. "
        "No identity of pointwise zero sets is asserted."
    )
    output["transport_majorant"] = "b" if auxiliary_gap else "H*I+b"
    output["weighted_minus_equal_weight_exact_degree"] = (
        330 if source_name == "direct105.json" else 358
    ) if auxiliary_gap else exact_degree - 6
    output["weight_comparison_reference"] = "Restore weight9 at the same current majorant."
    if auxiliary_gap:
        output["pinned_parent_minus_candidate_exact_degree"] = parent["exact_degree"]
    degrees = {name: 1 for name in parent["witnesses"]}
    degrees.update({name: 0 for name in parent["fixed_numerals"]})
    for name, op, aa, bb in output["source"]:
        da, db = (degrees[x] if isinstance(x, str) else 0 for x in (aa, bb))
        degrees[name] = da + db if op == "*" else max(da, db)
    output["syntactic_degree"] = degrees[output["output"]]
    output["register_degrees"] = {key: degrees[key] for key in parent["register_degrees"] if key in degrees}
    require(len(output["source"]) == count, "new source count")
    return output


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    targets = {
        "equation98.json": make("zero99.json", 98, 368),
        "equation104.json": make("direct105.json", 104, 340),
        "equation96.json": make("zero99.json", 96, 360, auxiliary_gap=True),
        "equation102.json": make("direct105.json", 102, 332, auxiliary_gap=True),
    }
    for name, value in targets.items():
        data = render(value)
        path = ROOT / name
        if args.check:
            require(path.read_bytes() == data, name)
        else:
            path.write_bytes(data)
        print(name, len(value["source"]), value["operation_breakdown"])


if __name__ == "__main__":
    main()
