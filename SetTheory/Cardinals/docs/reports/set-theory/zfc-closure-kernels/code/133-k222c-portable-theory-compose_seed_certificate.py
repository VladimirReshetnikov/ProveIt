#!/usr/bin/env python3
"""Extend the pinned merged-G proof DAG by the exact seed-bundle roots.

The expressions V, E and T are arbitrary native formula codes.  Here E is
the old equality helper and T = Q(c, I(H, N(W))).  The old seed bundle is
N(I(V, I(E, T))); deleting its helper gives N(I(V, T)).

This generator is separate from the inherited independent DAG checker.
It adds no proof rules.  Every added root is one ordinary TAUT leaf.
"""
import argparse
import hashlib
import json
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("predecessor_proof", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    raw = args.predecessor_proof.read_bytes()
    proof = json.loads(raw)
    falsehood = ("rel", 0, 0)
    imp = lambda x, y: ("imp", x, y)
    neg = lambda x: imp(x, falsehood)
    v, e, t = (("opaque", name) for name in ("V", "E", "T"))
    old = neg(imp(v, imp(e, t)))
    new = neg(imp(v, t))
    roots = {
        "seed_old_bundle_to_new_bundle": imp(old, new),
        "seed_old_bundle_projects_helper": imp(old, e),
        "seed_new_bundle_and_helper_to_old_bundle": imp(new, imp(e, old)),
    }
    for name, formula in roots.items():
        if name in proof["roots"]:
            raise ValueError("Root already exists: " + name)
        formula_index = len(proof["formulas"])
        node_index = len(proof["proof_nodes"])
        proof["formulas"].append(formula)
        proof["proof_nodes"].append(
            {"rule": "TAUT", "formula": formula_index, "args": []}
        )
        proof["roots"][name] = node_index
    proof["seed_composition"] = {
        "predecessor_sha256": hashlib.sha256(raw).hexdigest(),
        "old_bundle": old,
        "new_bundle": new,
        "interpretation": {
            "V": "membership vacuity",
            "E": "equality helper Eq(a,b) -> Q(RelCode(a,b),Eq(a,b))",
            "T": "Q(c, I(H, N(W))) for the literal seed closure and request",
        },
        "scope": "Uniform propositional substitution roots. G interderivations remain unchanged. Source/row coverage and K_s calibration are separate obligations.",
    }
    encoded = (json.dumps(proof, separators=(",", ":")) + "\n").encode()
    args.output.write_bytes(encoded)
    print(json.dumps({
        "status": "GENERATED_SEED_COMPOSITION_CERTIFICATE",
        "nodes": len(proof["proof_nodes"]),
        "formulas": len(proof["formulas"]),
        "roots": len(proof["roots"]),
        "sha256": hashlib.sha256(encoded).hexdigest(),
    }, indent=2))


if __name__ == "__main__":
    main()
