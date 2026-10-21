#!/usr/bin/env python3
"""Check the distributed bytes and their recorded evidence bindings.

This is an integrity audit, not a substitute for compiling the formal proofs.
Run it before rebuilding or editing distributed files.
"""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parent


def read_json(path):
    return json.loads(path.read_text())


def sha(data):
    return hashlib.sha256(data).hexdigest()


def require(condition, message):
    if not condition:
        raise SystemExit("FAIL: " + message)


def check_submanifest(folder):
    entries = read_json(folder / "manifest.json")
    for rel, expected in entries.items():
        expected_hash = expected if isinstance(expected, str) else expected["sha256"]
        require(sha((folder / rel).read_bytes()) == expected_hash,
                "subpackage hash: " + str(folder.name + "/" + rel))
    return len(entries)


def main():
    manifest = read_json(ROOT / "manifest.json")
    for rel, expected in manifest["files"].items():
        path = ROOT / rel
        require(not Path(rel).is_absolute() and ".." not in Path(rel).parts,
                "unsafe manifest path")
        require(path.is_file(), "missing file: " + rel)
        data = path.read_bytes()
        require(len(data) == expected["bytes"], "size mismatch: " + rel)
        require(sha(data) == expected["sha256"], "hash mismatch: " + rel)

    counts = {}
    for sub in ("balanced_lookup", "state_search"):
        counts[sub + "_manifest_files"] = check_submanifest(ROOT / sub)

    balanced = ROOT / "balanced_lookup"
    receipt = read_json(balanced / "evidence/result.json")
    for entry in receipt["results"]:
        rel = entry["file"]
        if rel == "deps/K230/RMEquiv.v":
            data = (balanced / "deps/K230/RMEquiv.rocq91.v").read_bytes()
            before = b"From K230 Require Import RM."
            require(data.count(before) == 1, "compatibility import anchor")
            data = data.replace(before, before + b"\nRequire Import Compat818.")
        else:
            data = (balanced / rel).read_bytes()
        require(sha(data) == entry["source_sha256"], "balanced source: " + rel)
        log = balanced / "evidence" / (rel.replace("/", "_") + ".log")
        require(sha(log.read_bytes()) == entry["log_sha256"], "balanced log: " + rel)
        require(entry["exit_code"] == 0, "balanced compilation status")
    generic = receipt["recursive_generic_check"]
    require(generic["target"] == "BalancedBisim" and generic["exit_code"] == 0,
            "generic recursive scope/status")
    require(sha((balanced / "evidence/coqchk_BalancedBisim.log").read_bytes())
            == generic["log_sha256"], "generic recursive log")
    counts["balanced_compile_bindings"] = len(receipt["results"])

    marker = ROOT / "marker_certificate"
    receipt = read_json(marker / "verification-final/receipt.json")
    for rel, expected in receipt["sources"].items():
        require(sha((marker / rel).read_bytes()) == expected, "marker source: " + rel)
    require(receipt["success"] and all(x["returncode"] == 0 for x in receipt["commands"]),
            "marker compilation status")
    require(receipt["closed_assumption_reports"] == 6, "marker assumption reports")
    mapping = read_json(marker / "M125.canonicalization.json")
    for filename, key in (("M125.tm", "native_sha256"), ("M125.dense.tm", "dense_sha256")):
        require(sha((marker / filename).read_bytes()) == mapping[key], filename)
    counts["marker_compile_bindings"] = len(receipt["sources"])

    credit = ROOT / "zero_credit"
    receipt = read_json(credit / "verification-final/receipt.json")
    require(sha((credit / "CantorCredit.v").read_bytes()) == receipt["source_sha256"],
            "credit source")
    require(all(x["exit_code"] == 0 for x in receipt["steps"]),
            "credit compilation status")
    require(receipt["closed_assumption_reports"] == 9, "credit assumption reports")
    counts["credit_compile_bindings"] = 1

    search = ROOT / "state_search"
    provenance = read_json(search / "provenance.json")
    require(provenance["repository_commit"] == manifest["repository_commit"],
            "search repository pin")
    for rel, expected in provenance["sources"].items():
        require(sha((search / rel).read_bytes()) == expected, "executed search source: " + rel)
    entries = read_json(search / "results.json")
    pairs = actions = survivors = 0
    for entry in entries:
        match = re.fullmatch(r"RESULT pairs (\d+) actions (\d+) partial (\d+) surviving_pairs (\d+)\s*",
                             entry["stdout"])
        require(match is not None, "search count format")
        pairs += int(match[1])
        actions += int(match[2])
        survivors += int(match[4])
        require((entry["context_depth"], entry["max_steps"], entry["max_nodes"])
                == (4, 45, 200), "search bounds")
    require((len(entries), pairs, actions, survivors) == (21, 155277, 133827040, 0),
            "search totals")
    counts["search_tables"] = len(entries)
    counts["search_pairs"] = pairs
    counts["search_action_checks"] = actions
    counts["search_survivors"] = survivors

    print(json.dumps({
        "status": "PASS_DISTRIBUTED_BYTES_AND_RECORDED_BINDINGS",
        "files": len(manifest["files"]),
        "repository_commit": manifest["repository_commit"],
        "checks": counts,
        "scope": "Integrity audit only; no proof-assistant run is implied by this command."
    }, indent=2))


if __name__ == "__main__":
    main()
