#!/usr/bin/env python3
"""Read-only source/receipt audit for the pinned K215 simplification baseline.

This script parses saved metadata and hashes current sources. It does not run a
proof compiler or an upstream script and does not inspect reusable proof objects.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import tarfile
from pathlib import Path

PIN = "57541fe0cfe3af62b4cb58747d8d1d7c16b338d5"
ZFC = Path("Computability/BusyBeaver/Research/ZFC")
SIMPL = ZFC / "k225-formal/verification/k215/simplification"
LEAN = Path("Computability/BusyBeaver/Lean/BusyBeaver/ZFC")


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def repo_path(record: dict) -> str:
    for marker in ("/Proofs/", "/candidate/"):
        if marker in record["source"]:
            return record["source"].split(marker, 1)[1]
    raise ValueError("Unrecognized archived source path: " + record["source"])


def imports(text: str) -> list[str]:
    result = []
    for line in text.splitlines():
        if line.startswith("import "):
            result.extend(line.split("--", 1)[0].split()[1:])
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    repo = args.repo.resolve()
    head = subprocess.check_output(["git", "-C", str(repo), "rev-parse", "HEAD"], text=True).strip()
    archive = repo / SIMPL / "phase12/lean/execution.tar.gz"
    with tarfile.open(archive, "r:gz") as saved:
        inventory = json.load(saved.extractfile("execution/inventory.json"))
        logs = {
            name: saved.extractfile("execution/audits/" + name + ".log").read().decode()
            for name in ("EndpointAudit215", "K215Audit")
        }
    rows = {row["module"]: row for row in inventory["modules"]}
    current = {}
    missing = []
    mismatches = []
    for module, row in rows.items():
        relative = repo_path(row)
        path = repo / relative
        if not path.is_file():
            missing.append(relative)
            continue
        data = path.read_bytes()
        text = data.decode()
        entry = {
            "path": relative,
            "bytes": len(data),
            "lines": len(text.splitlines()),
            "sha256": sha(data),
            "matches_saved_source": sha(data) == row["source_sha256"],
            "imports": imports(text),
        }
        # Explicit `Init` can be a standalone declaration; the archived parser
        # also includes it. Everything else is a project import.
        if entry["imports"] != row["imports"]:
            entry["archived_imports"] = row["imports"]
        if not entry["matches_saved_source"]:
            mismatches.append(relative)
        current[module] = entry

    def closure(target: str) -> set[str]:
        found: set[str] = set()
        pending = [target]
        while pending:
            name = pending.pop()
            if name in found or name not in rows:
                continue
            found.add(name)
            pending.extend(rows[name]["imports"])
        return found

    endpoint = closure("BusyBeaver.ZFC.KEndpoint215")
    pair = ["BusyBeaver.ZFC.DominatedImplication", "BusyBeaver.ZFC.Lukasiewicz"]
    proposal_dir = repo / SIMPL / "phase12/upstream-merge/inputs/Lean/BusyBeaver/ZFC"
    proposed_pair = {}
    for module in pair:
        path = proposal_dir / (module.rsplit(".", 1)[1] + ".lean")
        data = path.read_bytes()
        proposed_pair[module] = {
            "path": str(path.relative_to(repo)),
            "bytes": len(data),
            "lines": len(data.decode().splitlines()),
            "sha256": sha(data),
            "status": "archived proposed source; this script does not check Lean",
        }
    old_pair_bytes = sum(current[name]["bytes"] for name in pair)
    new_pair_bytes = sum(row["bytes"] for row in proposed_pair.values())
    old_pair_lines = sum(current[name]["lines"] for name in pair)
    new_pair_lines = sum(row["lines"] for row in proposed_pair.values())

    normalized_logs = {name: re.sub(r"\s+", " ", text).strip() for name, text in logs.items()}
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    axiom_profiles = {}
    for name, text in normalized_logs.items():
        profiles = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text)
        axiom_profiles[name] = {
            theorem: [x.strip() for x in names.split(",") if x.strip()]
            for theorem, names in profiles
        }
        for theorem, axioms in axiom_profiles[name].items():
            if not set(axioms) <= allowed:
                raise ValueError("Unexpected saved axiom profile: " + theorem)

    rocq_dir = repo / SIMPL / "phase2/rho8-global/rocq"
    rocq_result = json.loads((rocq_dir / "result.json").read_text())
    result = {
        "scope": "Fresh read-only source hashes, graph traversal, and reading archived proof logs; no new compiler invocation or live-object audit.",
        "pin": PIN,
        "current_head": head,
        "pin_matches": head == PIN,
        "phase12_archive_sha256": sha(archive.read_bytes()),
        "primary_inventory_modules": len(rows),
        "endpoint_closure_modules": len(endpoint),
        "endpoint_source_bytes": sum(current[name]["bytes"] for name in endpoint) if endpoint <= current.keys() else None,
        "endpoint_source_lines": sum(current[name]["lines"] for name in endpoint) if endpoint <= current.keys() else None,
        "missing_sources": missing,
        "mismatching_sources": mismatches,
        "all_materialized_sources_match": not mismatches,
        "old_pair": {name: current[name] for name in pair},
        "archived_proposed_pair": proposed_pair,
        "pair_comparison": {
            "old_bytes": old_pair_bytes, "proposed_bytes": new_pair_bytes,
            "reduction_bytes": old_pair_bytes - new_pair_bytes,
            "old_lines": old_pair_lines, "proposed_lines": new_pair_lines,
            "reduction_lines": old_pair_lines - new_pair_lines,
            "old_private_cd_count": len(re.findall(r"^private theorem cd_\d+", (repo / LEAN / "Lukasiewicz.lean").read_text(), re.M)),
        },
        "saved_endpoint_axiom_profiles": axiom_profiles,
        "rocq_saved_result": rocq_result,
        "current_sources": current,
        "endpoint_closure": sorted(endpoint),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k not in ("current_sources", "endpoint_closure", "rocq_saved_result")}, indent=2))


if __name__ == "__main__":
    main()
