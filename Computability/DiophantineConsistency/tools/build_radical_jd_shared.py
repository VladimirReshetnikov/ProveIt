#!/usr/bin/env python3
"""Three exact gate savings in the110-term J,D-basis radical evaluator."""
import argparse
import json
from pathlib import Path

from build_shared_products66 import encoded, evaluate, rejects_mutation, sha, transform, verify
from build_shared_products71 import BINDING, PORTS, fixed_values
from review_proposal_frontier import audit, require

ROOT = Path(__file__).resolve().parents[1]
DEST = ROOT / "candidates/radical-jd-shared"
PIN = "56e8629e1590157e608d5ffafcf3943b925562578fba4854c81d443ed2e54f93"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    raw = (DEST / "source/parent.json").read_bytes()
    require(sha(raw) == PIN, "pinned arriving726-operation circuit")
    parent = json.loads(raw)
    require(parent["total_operations"] == 726 and parent["exact_degree"] == 1158228, "parent metrics")
    child, certificate = transform(parent, degree=1158228, fixed_binding=BINDING)
    identities = verify(parent, child, certificate)
    require(child["total_operations"] == 723, "three shared-product savings")
    require(rejects_mutation(parent, child, certificate), "operation-preserving corruption rejected")
    binding_raw = (PORTS / "COEFFICIENT_BINDING.json").read_bytes()
    fixed = fixed_values(parent, json.loads(binding_raw))
    for modulus in (65537, 1000000007, 2147483647):
        for seed in range(20):
            values = {v: seed*(j+3)-17 for j, v in enumerate(child["variables"])}
            before, after = evaluate(parent, values, fixed, modulus), evaluate(child, values, fixed, modulus)
            require(before[parent["output"]] == after[child["output"]], "actual output diagnostic")
            for name, index in parent["named_nodes"].items():
                require(before[index] == after[child["named_nodes"][name]], "actual named-value diagnostic")
    child_raw = encoded(child)
    certificate.update(identities=identities, parent_sha256=PIN, child_sha256=sha(child_raw),
                       fixed_binding_sha256=sha(binding_raw), modular_assignments=60,
                       scope="Exact ring-polynomial identity; parent ordinary degree/calibration inherited. No Lean.")
    files = {"equation9.json": child_raw, "rewrite.json": encoded(certificate),
        "REVIEW.json": encoded(dict(status="PASS", variables=9, domain="positive integers",
            operations=723, parent_operations=726, exact_degree=1158228,
            output_polynomial_identical=True, fixed_binding_sha256=sha(binding_raw),
            modular_assignments=60, corruption_rejected=True,
            scope="Three exact local product/cancellation savings; inherited source/native/internal-ZFC boundary."))}
    files["MANIFEST.json"] = encoded({name: sha(value) for name, value in sorted(files.items())})
    for name, value in files.items():
        path = DEST / name
        if args.check:
            require(path.read_bytes() == value, f"reproduce {name}")
        else:
            path.write_bytes(value)
    audit(("../candidates/radical-jd-shared/equation9.json", 9, "+", 1158228, 723))
    print(files["REVIEW.json"].decode(), end="")


if __name__ == "__main__":
    main()
