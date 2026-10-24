#!/usr/bin/env python3
"""Replay monic-coordinate eliminations without importing the optimizer."""
from __future__ import annotations
import argparse
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path

from audit_common_radix import add, mul, scalar, var, polynomial, sparse, require


def digest(obj):
    return sha256((json.dumps(obj, sort_keys=True, separators=(",", ":"))+"\n").encode()).hexdigest()


def replace_variable(poly, variable, value):
    out = {}
    for mon, c in poly.items():
        term = scalar(c)
        for i in mon:
            term = mul(term, value if i == variable else var(i))
        out = add(out, term)
    return out


def verify(parent, child, certificate, check_hashes=True):
    if check_hashes:
        require(digest(parent) == certificate["input_sha256"], "input polynomial hash mismatch")
        require(digest(child) == certificate["output_sha256"], "output polynomial hash mismatch")
    require(parent["domain"] == child["domain"], "domain changed in projection")
    natural = parent["domain"] == "nonnegative integers"
    require(natural or parent["domain"] in ("integers", "unrestricted integers", "all integers"),
            "unknown integer domain")
    n = len(parent["variables"])
    rows = {j: polynomial(r["terms"]) for j, r in enumerate(parent["residuals"])}
    alive = set(range(n))
    degrees = {}
    for step_number, step in enumerate(certificate["steps"]):
        variable, row_id = step["variable"], step["row_id"]
        require(variable in alive and row_id in rows, "elimination target no longer exists")
        value = polynomial(step["restoration"])
        require(all(i in alive and i != variable for mon in value for i in mon),
                "restoration uses deleted or self coordinate")
        d = max(map(len, value), default=0)
        require(d <= 2, "restoration degree exceeds two")
        if natural:
            require(all(c >= 0 for c in value.values()), "restoration may be negative")
        definition = add(var(variable), value, -1)
        require(rows[row_id] in (definition, {m: -c for m, c in definition.items()}),
                f"step {step_number}: deleted residual is not the claimed monic equation")
        updated = {}
        for j, r in rows.items():
            if j == row_id:
                continue
            p = replace_variable(r, variable, value)
            require(max(map(len, p), default=0) <= 2, "projection raises residual degree")
            if p:
                updated[j] = p
        rows = updated
        alive.remove(variable)
        degrees[str(d)] = degrees.get(str(d), 0)+1
    used = sorted({i for p in rows.values() for mon in p for i in mon})
    require(used == certificate["retained_original_variables"], "retained coordinate map mismatch")
    require(sorted(alive-set(used)) == certificate["unconstrained_removed"], "free-coordinate map mismatch")
    require(sorted(rows) == certificate["retained_original_rows"], "retained row map mismatch")
    remap = {old: new for new, old in enumerate(used)}
    expected = [{"label": parent["residuals"][j]["label"],
                 "terms": [[c, [remap[i] for i in mon]] for mon, c in sorted(p.items())]}
                for j, p in sorted(rows.items())]
    require(child["residuals"] == expected, "output residuals differ from exact substitutions")
    require(child["variables"] == [parent["variables"][i] for i in used], "output variable map mismatch")
    return {"status": "PASS", "domain": parent["domain"],
            "verified_eliminations": len(certificate["steps"]),
            "restoration_degree_counts": degrees,
            "variables": len(used), "quadratic_residuals": len(rows)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("parent_equation", type=Path)
    parser.add_argument("child_directory", type=Path)
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()
    parent = json.loads(args.parent_equation.read_text())
    child = json.loads((args.child_directory / "equation.json").read_text())
    certificate = json.loads((args.child_directory / "terminal_elimination_certificate.json").read_text())
    result = verify(parent, child, certificate)
    require(certificate["steps"], "no elimination steps to check")
    corrupted = deepcopy(certificate)
    corrupted["steps"][0]["restoration"][0][0] += 1
    rejected = False
    try:
        verify(parent, child, corrupted)
    except ValueError:
        rejected = True
    require(rejected, "corrupted restoration was accepted")
    result["mutated_restoration_rejected"] = True
    result["scope"] = "exact monic polynomial projection and reverse restoration; no optimizer imported"
    payload = json.dumps(result, indent=2, sort_keys=True)+"\n"
    if args.receipt:
        args.receipt.write_text(payload)
    print(payload)


if __name__ == "__main__":
    main()
