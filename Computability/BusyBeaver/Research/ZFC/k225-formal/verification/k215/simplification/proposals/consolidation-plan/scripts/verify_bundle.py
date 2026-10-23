#!/usr/bin/env python3
"""Verify distributed hashes and the bindings of accepted component receipts.

This does not run Lean or Coq, establish semantic correctness, or authenticate a
publisher. It detects package corruption and mismatches between the distributed
sources, source snapshots, logs, measurements, and recorded successful checks.
Python 3.11+ standard library only; no network or repository writes.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

PIN = "cbf94cb552a3b49509e0eee80e7455d4eb5974c6"
ROOT = Path(__file__).resolve().parent.parent


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path):
    return json.loads(path.read_text())


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit("FAIL: " + message)


def hash_is(path: Path, expected: str) -> None:
    require(path.is_file(), f"Missing file: {path}")
    require(digest(path) == expected, f"Hash mismatch: {path}")


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo", type=Path, help="Also bind original source hashes to this checkout")
    args = ap.parse_args()
    manifest = read(ROOT / "MANIFEST.json")
    require(manifest["repository_commit"] == PIN, "Manifest source pin")
    for relative, entry in manifest["files"].items():
        path = (ROOT / relative).resolve()
        require(path.is_relative_to(ROOT), f"Unsafe manifest path: {relative}")
        hash_is(path, entry["sha256"])
        require(path.stat().st_size == entry["bytes"], f"Size mismatch: {relative}")

    native = ROOT / "lean-native"
    receipt = read(native / "build02/receipt.json")
    require(receipt["status"] == "PASS" and receipt["repository_commit"] == PIN,
            "Native receipt status/pin")
    require(receipt["project_modules"] == 107 and receipt["audit_modules"] == 2,
            "Native compile scope")
    require(len(receipt["records"]) == 109, "Native record count")
    for rec in receipt["records"]:
        require(rec["exit_code"] == 0, f"Native failed record: {rec['module']}")
        snapshot = native / "build02/sources" / (rec["module"].replace(".", "/") + ".lean")
        hash_is(snapshot, rec["source_sha256"])
        require(snapshot.stat().st_size == rec["source_bytes"], f"Native byte count: {snapshot}")
        require(len(snapshot.read_bytes().splitlines()) == rec["source_lines"],
                f"Native line count: {snapshot}")
        log = native / "build02" / rec["log"]
        hash_is(log, rec["log_sha256"])
        require("sorryAx" not in log.read_text(), f"Admitted dependency in log: {log}")
        origin = rec["source"]
        if origin.startswith("packet:"):
            hash_is(native / origin.removeprefix("packet:"), rec["source_sha256"])
        elif args.repo:
            hash_is(args.repo / origin.removeprefix("repo:"), rec["source_sha256"])

    baseline = read(ROOT / "evidence/baseline-census.json")
    proposed = read(ROOT / "evidence/proposed-census.json")
    compared = read(native / "closure-census.json")
    expected = [(baseline, compared["baseline"], (174, 1752650, 37648)),
                (proposed, compared["native"], (173, 1744292, 37483))]
    for independent, component, counts in expected:
        observed = (independent["project_modules"], independent["source_bytes"],
                    independent["physical_lines"])
        require(observed == counts, "Independent census totals")
        require((component["module_count"], component["bytes"], component["lines"]) == counts,
                "Component census totals")
        for record in independent["modules"]:
            other = component["modules"][record["module"]]
            require(record["sha256"] == other["sha256"], "Census source hash agreement")
            require(record["imports"] == other["imports"], "Census import agreement")
    require(all(read(native / "split-audit.json")["checks"].values()), "Source split checks")

    transport = ROOT / "lean-termination"
    treceipt = read(transport / "evidence/replay.json")
    ledger = read(transport / "source-hashes.json")
    require(treceipt["complete"] and treceipt["pin"] == PIN == ledger["pin"],
            "Termination receipt status/pin")
    for rec in treceipt["runs"]:
        require(rec.get("exit_code") == 0 or rec.get("reused_exact_baseline_object") is True,
                f"Termination failed record: {rec['module']}")
        require("sorryAx" not in rec.get("output", ""), "Termination admitted dependency")
        if rec["module"] == "Audit":
            source = transport / "audits/Audit.lean"
        elif rec["lane"] == "patched" and not rec.get("reused_exact_baseline_object"):
            source = transport / "lean" / (rec["module"].replace(".", "/") + ".lean")
        else:
            require(rec["source_sha256"] == ledger["modules"][rec["module"]],
                    "Termination baseline receipt/ledger")
            source = None
        if source:
            hash_is(source, rec["source_sha256"])
    require(sum(r.get("reused_exact_baseline_object", False) for r in treceipt["runs"]) == 12,
            "Termination reuse count")
    require(sum(r["lane"] == "baseline" and r["module"] != "Audit"
                for r in treceipt["runs"]) == 13, "Termination baseline count")

    rocq = ROOT / "rocq-runtime"
    creceipt = read(rocq / "verification.json")
    require(creceipt["status"] == "PASS_STANDALONE_COQ_KERNEL", "Coq receipt status")
    require("8.16.1" in creceipt["compiler_version"], "Coq recorded toolchain")
    for name, expected_hash in creceipt["sources"].items():
        hash_is(rocq / name, expected_hash)
    hash_is(rocq / "check.py", creceipt["driver_sha256"])
    for rec in creceipt["records"]:
        require(rec["exit_code"] == 0, "Coq failed record")
        hash_is(rocq / rec["log"], rec["log_sha256"])
    require(sum(rec["closed_reports"] for rec in creceipt["records"]) == 6,
            "Coq assumption-report count")

    if args.repo:
        repo = args.repo.resolve()
        commit = subprocess.check_output(["git", "-C", str(repo), "rev-parse", "HEAD"],
                                         text=True).strip()
        require(commit == PIN, "Repository HEAD differs from pin")
        for rec in baseline["modules"]:
            hash_is(repo / rec["path"], rec["sha256"])
        for key in ["table", "source"]:
            rec = baseline["machine"][key]
            hash_is(repo / rec["path"], rec["sha256"])
        for module, expected_hash in ledger["modules"].items():
            hash_is(repo / ledger["source_root"] / (module.replace(".", "/") + ".lean"),
                    expected_hash)
        census = read(rocq / "runtime_audit.json")
        for rec in census["inputs"].values():
            hash_is(repo / rec["path"], rec["sha256"])

    print(json.dumps({
        "status": "PASS_PACKAGE_AND_RECEIPT_BINDINGS",
        "manifest_files": len(manifest["files"]),
        "native_successful_compilations": 109,
        "termination_baseline_project_modules": 13,
        "termination_exact_dependency_reuses": 12,
        "coq_closed_assumption_reports": 6,
        "repository_sources_checked": bool(args.repo),
        "kernel_replay_performed_by_this_script": False
    }, indent=2))


if __name__ == "__main__":
    main()
