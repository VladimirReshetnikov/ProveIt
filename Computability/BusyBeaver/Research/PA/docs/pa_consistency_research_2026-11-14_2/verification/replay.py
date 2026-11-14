#!/usr/bin/env python3
"""Network-free checks of this delivery; not a consistency-equivalence proof.

Run with assertions enabled. The larger optional physical replay is documented
in research/physical/SEARCH_NOTES.txt. This check never modifies frozen evidence.
"""
from pathlib import Path
import collections
import hashlib
import importlib.util
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
PIN = "567266818aaeceb0f3a8f82debf303c8d84bddaf"


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def read(path):
    return json.loads((ROOT / path).read_text())


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    assert __debug__, "Do not run with Python -O."
    summary = read("comparison/SUMMARY.json")
    assert summary["snapshot"] == PIN
    packets = read("comparison/packet_ledger_61.json")["packets"]
    assert len(packets) == summary["packet_total"] == 61
    assert summary["filed_packets"] == 55
    assert summary["top_level_incoming_archives"] == 6
    literal = read("comparison/fresh_literal/census.json")
    for key, value in literal["summary"].items():
        assert summary[key] == value, (key, summary[key], value)
    assert not literal["summary"]["errors"]
    graphs = read("comparison/all_graph_classes.json")
    assert len(graphs) == 531
    by_size = collections.Counter(g["states"] for g in graphs)
    assert by_size[194] == 49 and by_size[195] == 22 and by_size[196] == 102
    assert sum(n for size, n in by_size.items() if size >= 10) == 523

    inv = module("literal_inventory", ROOT / "comparison/literal_inventory.py")
    frontier = read("comparison/frontier194.json")["classes"]
    assert len(frontier) == 49
    statuses = collections.Counter(x["status"] for x in frontier)
    assert dict(statuses) == summary["frontier194_status_counts"]
    seen = set()
    for item in frontier:
        path = ROOT / "comparison" / item["table_file"]
        raw = path.read_bytes()
        assert sha(raw) == item["representative_sha256"], path
        data = inv.parse_table(raw)
        assert data is not None and len(data[1]) == 194, path
        rooted = inv.canonical(data, item["start"])
        assert rooted is not None, (path, "start does not span the table")
        assert sha(repr(rooted).encode()) == item["rooted_graph_hash"], path
        forms = [c for q in sorted(data[1])
                 if (c := inv.canonical(data, q)) is not None]
        graph = sha(repr(min(forms)).encode())
        assert graph == item["graph_hash"] and graph not in seen, path
        seen.add(graph)

    offsets = module("check_offsets", ROOT / "verification/offset_obstructions/check_offsets.py")
    offset_results = []
    for path in sorted((ROOT / "verification/offset_obstructions/evidence").glob("offset_*.json")):
        obj = json.loads(path.read_text())
        assert offsets.build(obj["offset"]) == obj, path
        offset_results.append(offsets.check(obj))
    assert len(offset_results) == 20
    for k in range(1, 10001):
        e = 3 * k + 1
        assert offsets.E(e, 2 * k, 0) == offsets.M(k, k)
        assert offsets.E(e, 3 * k, k) == offsets.M(2 * k, 2 * k)

    run = subprocess.run([sys.executable, "-B", str(ROOT / "verification/check_logic_obstructions.py")],
                         check=True, capture_output=True, text=True)
    primitive = module("primitive_verifier", ROOT / "research/rejected193_refutation/verify_primitive.py")
    primitive_result = primitive.verify(ROOT / "research/rejected193_refutation/primitive_proof.json")
    assert primitive_result["primitive_proof_steps"] == 73393
    assert primitive_result["final_conclusion"] == 1

    physical_root = ROOT / "research/physical"
    physical_manifest = read("research/physical/manifest.json")
    physical_receipt = read("research/physical/receipts/verified_searches_328.json")
    assert physical_manifest["commit"] == PIN
    for rel, digest in physical_manifest["files"].items():
        assert sha((physical_root / rel).read_bytes()) == digest, rel
    assert physical_receipt["status"] == "passed"
    assert physical_receipt["case_count"] == 328
    assert physical_receipt["all_expected_stdout_empty"] is True
    expected_cases = {x["case_id"]: x for x in physical_manifest["cases"]}
    assert len(expected_cases) == len(physical_receipt["cases"]) == 328
    for case in physical_receipt["cases"]:
        expected = expected_cases[case["case_id"]]
        assert case["pass"] is True and case["returncode"] == 0
        assert case["stdout"] == expected["expected_stdout"] == ""
        assert case["table_sha256"] == sha((physical_root / expected["table"]).read_bytes())
    for rel, digest in physical_receipt["code_sha256"].items():
        assert sha((physical_root / "code" / rel).read_bytes()) == digest, rel

    manifest = ROOT / "MANIFEST.sha256"
    checked = 0
    if manifest.exists():
        for line in manifest.read_text().splitlines():
            digest, rel = line.split("  ", 1)
            path = ROOT / rel
            assert path.is_file() and sha(path.read_bytes()) == digest, rel
            checked += 1

    result = {
        "status": "PASS",
        "snapshot": PIN,
        "deliveries": len(packets),
        "graph_classes": len(graphs),
        "frontier_tables_hash_start_and_graph_checked": len(frontier),
        "frontier_statuses": dict(statuses),
        "numeric_offset_certificates_checked": len(offset_results),
        "residue_one_pairing_checks": 10000,
        "inherited_primitive_refutation_steps_checked": primitive_result["primitive_proof_steps"],
        "physical_screen_receipts_bound_to_frozen_inputs": 328,
        "physical_search_reexecuted_by_this_quick_audit": False,
        "boolean_obstruction": run.stdout.strip(),
        "manifest_files_checked": checked,
        "proof_boundary": "Finite delivery audit. Offset certificates use declared derived rules. No new machine below 194 states or proof-assistant endpoint is claimed."
    }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
