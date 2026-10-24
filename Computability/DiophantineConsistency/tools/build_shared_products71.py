#!/usr/bin/env python3
"""Transfer the exact shared-product reduction to the lower-degree package71.

The parent package is read as inert JSON only. Its mathematical interfaces
and degree certificate are inherited; no delivered executable is imported.
"""
import argparse
import copy
import gzip
import hashlib
import json
from pathlib import Path

from build_shared_products66 import encoded, evaluate, rejects_mutation, sha, transform, verify
from review_proposal_frontier import audit, require

ROOT = Path(__file__).resolve().parents[1]
PARENT = ROOT / "con-zfc-diophantine-forms/71-determinant-guards/nine_positive"
PORTS = ROOT / "con-zfc-diophantine-forms/31-sun10/coefficients"
DEST = ROOT / "candidates/order7-shared-products"
PINS = {
    "positive": "f5d00f414abd0c61e1d7f11b682474f63bc34b08e44730de20a5829e2a613e25",
    "natural": "611c430bad123448454edf82fae10ce895d97f04b9b637a88294ea71abd55222",
}
BINDING = "../../con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_BINDING.json"


def fixed_values(body, binding):
    ports = {}
    for entry in binding["files"]:
        raw = gzip.decompress((PORTS / entry["file"]).read_bytes())
        require(sha(raw) == entry["sha256"], "complete original31 coefficient payload")
        ports[entry["port"]] = int.from_bytes(raw, "little")
    values = [ports[n] for n in ("beta", "K", "MC", "MF_source")]
    require([v.bit_length() for v in values] == body["port_bit_lengths"], "whole parent tuple dimensions")
    used = {n["name"] for n in body["nodes"] if n["kind"] == "fixed"}
    fixed = {}
    for entry in body["coefficient_recipes"]:
        if entry["name"] not in used:
            continue
        result = 0
        for term in entry["terms"]:
            value = term["coefficient"]
            for port, power in zip(values, term["powers"]):
                value *= port**power
            result += value
        fixed[entry["name"]] = result
    fixed["base_scale"] = 1 << body["base_scale_exponent"]
    fixed["threshold_scale"] = 1 << body["threshold_scale_exponent"]
    require(set(fixed) == used, "every fixed leaf bound, without mixing tuples")
    return fixed


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    binding_raw = (PORTS / "COEFFICIENT_BINDING.json").read_bytes()
    binding = json.loads(binding_raw)
    files, rows = {}, []
    for domain, old_cost, new_cost in (("positive", 478, 475), ("natural", 485, 482)):
        raw = (PARENT / "generated" / f"composed9_{domain}.json").read_bytes()
        require(sha(raw) == PINS[domain], "pinned original package71 circuit")
        parent = json.loads(raw)
        require(parent["exact_degree"] == 1379730 and parent["total_operations"] == old_cost, "parent metrics")
        child, certificate = transform(parent, degree=1379730, fixed_binding=BINDING)
        identities = verify(parent, child, certificate)
        require(child["total_operations"] == new_cost, "three-gate saving")
        require(rejects_mutation(parent, child, certificate), "exact identity corruption control")
        fixed = fixed_values(child, binding)
        for modulus in (65537, 1000000007, 2147483647):
            for seed in range(20):
                values = {v: seed*(i+3)-17 for i, v in enumerate(child["variables"])}
                before, after = evaluate(parent, values, fixed, modulus), evaluate(child, values, fixed, modulus)
                for name, index in parent["named_nodes"].items():
                    require(before[index] == after[child["named_nodes"][name]], "actual named-register diagnostic")
                require(before[parent["output"]] == after[child["output"]], "actual output diagnostic")
        child_raw = encoded(child)
        certificate.update(parent_sha256=sha(raw), child_sha256=sha(child_raw), identities=identities,
                           fixed_binding_sha256=sha(binding_raw), modular_assignments=60,
                           corruption_control="A addition changed to subtraction; exact check rejects",
                           scope="Same ring polynomial by four local identities and complete remap; no Lean work.")
        files[f"order7_{domain}.json"] = child_raw
        files[f"{domain}_rewrite.json"] = encoded(certificate)
        rows.append(dict(domain=domain, variables=9, operations=new_cost, removed_operations=3,
                         exact_degree=1379730, sha256=sha(child_raw)))
    files["REVIEW.json"] = encoded(dict(status="PASS", circuits=rows,
        fixed_binding_sha256=sha(binding_raw),
        degree_reason="Exact polynomial identity transfers the pinned package71 ordinary degree proof.",
        scope="Lower-degree nine-variable size reduction; inherited native/compiler/internal-ZFC boundaries unchanged."))
    files["MANIFEST.json"] = encoded({name: sha(raw) for name, raw in sorted(files.items())})
    for name, raw in files.items():
        path = DEST / name
        if args.check:
            require(path.read_bytes() == raw, f"reproduce {name}")
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(raw)
    for domain, cost in (("positive", 475), ("natural", 482)):
        audit((f"../candidates/order7-shared-products/order7_{domain}.json", 9,
               "+" if domain == "positive" else "N", 1379730, cost))
    print(json.dumps(dict(status="PASS", circuits=rows, files=len(files)), indent=2))


if __name__ == "__main__":
    main()
