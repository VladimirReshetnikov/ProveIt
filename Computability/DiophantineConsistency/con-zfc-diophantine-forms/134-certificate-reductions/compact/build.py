#!/usr/bin/env python3
"""Build the unscaled, quotient-normalized positive circuits.

Only JSON data are read from the frozen parent; no upstream program is run.
"""
from __future__ import annotations
import argparse
from collections import Counter
from copy import deepcopy
import json
import hashlib
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def compile_variant(parent: dict, weight: str) -> dict:
    old = parent["source"]
    dropped = {"q2", "q3", "mu", "muY", "P1", "mu2", "qm1Y", "q3Bt", "inner"}
    aliases = {"muY": "Y", "muY2": "Y2", "mu2": "Y2"}
    rows = []
    for name, op, left, right in old:
        if name in dropped:
            continue
        left, right = aliases.get(left, left), aliases.get(right, right)
        name = aliases.get(name, name)
        if name == "P1mu2":
            left, right = "bJ", "Y2"
        elif name == "mu2inner":
            left, right = "Y2", "Bt"
        elif name == "P1e":
            left, right = "bJ", "e"
        elif name == "brk":
            op = "+"
        elif name == "Znum":
            op = "-"
        rows.append([name, op, left, right])
        if name == "q":
            rows.extend([["q2", "*", "q", "q"],
                         ["q3", "*", "q2", "q"],
                         ["Y", "*", "q3", "s"]])
    result = {
        "name": "unscaled_" + weight,
        "domain": "strictly positive integers",
        "witnesses": ["s" if x == "Y" else x for x in parent["witnesses"]],
        "fixed_numerals": parent["fixed_numerals"],
        "coefficient_binding": deepcopy(parent["coefficient_binding"]),
        "source": rows,
        "output": "N",
        "operations": len(rows),
        "operation_breakdown": dict(sorted(Counter(r[1] for r in rows).items())),
        "exact_degree": 630 if weight == "V2" else 468,
        "transport_weight": "V^2" if weight == "V2" else "bV",
        "proof": "PROOF.md",
        "parent": "proof_sources/equation_84.json" if weight == "V2" else "proof_sources/equation_85.json",
        "status": "Ordinary mathematical proof composed with the pinned native/refutation calibration; no new end-to-end formal proof object.",
    }
    for meta in result["coefficient_binding"]["ports"].values():
        meta["parent_gzip_sha256"] = meta["gzip_sha256"]
        meta["gzip_sha256"] = hashlib.sha256((ROOT/"coefficients"/meta["file"]).read_bytes()).hexdigest()
    return result


def encode(x):
    return json.dumps(x, indent=2, ensure_ascii=False) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    results = []
    for num, weight, target in [(84, "V2", "equation78.json"), (85, "bV", "equation79.json")]:
        source = ROOT / "proof_sources" / f"equation_{num}.json"
        parent = json.loads(source.read_text())
        data = encode(compile_variant(parent, weight))
        path = ROOT / target
        if args.check:
            if path.read_text() != data:
                raise ValueError(f"Rebuild differs: {target}")
        else:
            path.write_text(data)
        results.append({"path": target, "bytes": len(data.encode()), "operation": "verified" if args.check else "created"})
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
