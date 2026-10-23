#!/usr/bin/env python3
"""Independently read the compact split DAGs, seals and signed fixed leaves.

This reuses only the independent DAG reader, never a candidate builder.
Reported degrees are transcribed; no degree proof or semantic theorem is
inferred here. Full reconstruction is the separate generator's --check mode.
"""
import gzip
import hashlib
import json

from review_proposal_frontier import ROOT, audit, require


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def main():
    family = ROOT / "candidates/split116-compact"
    rows = []
    for variant in ("compact57", "compact54"):
        instance = family / variant
        manifest = json.loads((instance / "MANIFEST.json").read_text())
        for name, expected in manifest.items():
            require(sha((instance / name).read_bytes()) == expected,
                    f"{variant}: manifest member {name}")
        binding = json.loads((instance / "fixed/BINDING.json").read_text())
        fixed_names = set()
        for record in binding["live_fixed_leaves"]:
            blob = (instance / record["path"]).read_bytes()
            raw = gzip.decompress(blob)
            require(sha(blob) == record["gzip_sha256"], "fixed gzip hash")
            require(sha(raw) == record["sha256"], "fixed raw hash")
            magnitude = int.from_bytes(raw, "little")
            require(len(raw) == record["bytes"], "fixed raw length")
            require(magnitude.bit_length() == record["bits"], "fixed bit length")
            require(record["sign"] in (-1, 0, 1), "fixed sign")
            require((magnitude == 0) == (record["sign"] == 0), "fixed zero sign")
            require(record["name"] not in fixed_names, "repeated fixed leaf")
            fixed_names.add(record["name"])
        for domain, operations, suffix in (("+", 473, "positive"), ("N", 480, "natural")):
            path = f"../candidates/split116-compact/{variant}/generated/split_116_{suffix}.json"
            row = audit((path, 9, domain, 1910404, operations))
            data = json.loads((instance / f"generated/split_116_{suffix}.json").read_text())
            live = {node["name"] for node in data["nodes"] if node["kind"] == "fixed"}
            require(live == fixed_names, f"{variant}: exact live fixed binding")
            row["instance"] = variant
            rows.append(row)
    result = dict(status="PASS", scope="Independent literal DAG/liveness/count audit, fixed-leaf bytes/hash readback and whole candidate manifest check. No unbounded theorem or new degree proof inferred.", circuits=rows)
    target = family / "INDEPENDENT_CIRCUIT_REVIEW.json"
    target.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(dict(status="PASS", instances=2, circuits=len(rows))))


if __name__ == "__main__":
    main()
