#!/usr/bin/env python3
"""Verify the selected source metrics, literal table counts, and file hashes.

This does not turn the larger experimental tables into certified machines.
Their precise limits are retained in the manifest and compilation receipts.
"""
from __future__ import annotations
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

import reconstruct_full_dn as reconstruct


def require(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    root = Path(__file__).resolve().parents[1]
    manifest = json.loads((root / "selected_results_manifest.json").read_text())
    for name, record in manifest["files"].items():
        raw = (root / name).read_bytes()
        require(hashlib.sha256(raw).hexdigest() == record["sha256"], "File hash mismatch: " + name)
        require(len(raw) == record["bytes"], "File length mismatch: " + name)
    spec = importlib.util.spec_from_file_location("source_builder", root / "vendor/build_zfc235.py")
    builder = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(builder)
    checks = []
    for result in manifest["selected_results"]:
        source = builder.tree(json.loads((root / result["source"]).read_bytes()))
        metrics = builder.metrics(source)
        builder.graph(builder.sites(source))
        for name in ("dag_nodes", "leaf_occurrences"):
            require(metrics[name] == result[name], result["name"] + ": incorrect " + name)
        if "table" in result:
            rows = {}
            for line in (root / result["table"]).read_text().splitlines():
                if not line or line.startswith("#"):
                    continue
                q, bit, write, direction, target = line.split()
                q, bit, write, target = map(int, (q, bit, write, target))
                require((q, bit) not in rows and bit in (0, 1) and write in (0, 1) and direction in ("L", "R"), "Malformed binary row")
                rows[q, bit] = (write, direction, target)
            states = {q for q, bit in rows}
            require(set(rows) == {(q, bit) for q in states for bit in (0, 1)}, "Incomplete working-state table")
            require({target for _, _, target in rows.values()} - states == {254}, "Unexpected halt convention")
            require(len(states) == result["working_states"], "Incorrect literal working-state count")
            receipt = json.loads((root / result["receipt"]).read_text())
            require(receipt["internal_decoder_contract_failures"] == [], "Rejected decoder source")
            require(receipt["simplified_working_states"] == len(states), "Incorrect receipt count")
        checks.append({"name": result["name"], "source_metrics": metrics, "scope": result["scope"]})
    raw, metrics = reconstruct.reconstruct(root / "inputs/sites225.json", root / "dn4/recipe4.json", root / "vendor/build_zfc235.py")
    require(raw == (root / "dn4/sites_full_dn4.json").read_bytes(), "DN4 reconstruction is not exact")
    summary = json.loads((root / "row_parameters/summary.json").read_text())
    for basis in ("original", "dn4"):
        selected = [x for x in summary if x["tag"].startswith(basis + "_")]
        require(len(selected) == 40, "Incorrect individual-row experiment total")
        require(min(x["dag_nodes"] for x in selected) == 212 and max(x["dag_nodes"] for x in selected) == 222, "Incorrect individual-row experiment range")
    print(json.dumps({"status": "PASS_SELECTED_ARTIFACT_HASHES_SOURCE_METRICS_AND_LITERAL_COUNTS", "checked_files": len(manifest["files"]), "checks": checks}, indent=2))


if __name__ == "__main__":
    main()
