#!/usr/bin/env python3
"""Quick offline gate for the delivered research archive.

Checks exact file integrity and the declared finite certificates. This does
not rebuild Coq/Lean or repeat 6.3 billion startup simulation moves.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def checked_run(arguments: list[str], cwd: Path) -> dict:
    env = os.environ.copy()
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    result = subprocess.run(
        [sys.executable, *arguments], cwd=cwd, env=env,
        text=True, capture_output=True, check=True,
    )
    try:
        output = json.loads(result.stdout)
    except json.JSONDecodeError:
        output = result.stdout.strip()
    return {"command": arguments, "exit_code": result.returncode, "result": output}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quick", action="store_true", help="run the offline quick gate (default)")
    args = parser.parse_args()
    if not __debug__:
        parser.error("assertions must be enabled; do not run Python with -O")

    manifest_path = ROOT / "SHA256SUMS.json"
    if not manifest_path.exists():
        raise SystemExit("Missing SHA256SUMS.json: use the complete delivered archive")
    manifest = json.loads(manifest_path.read_text())
    for relative, expected in manifest.items():
        candidate = ROOT / relative
        if not candidate.is_file() or sha256(candidate) != expected:
            raise SystemExit(f"Integrity mismatch: {relative}")

    spec = importlib.util.spec_from_file_location(
        "independent_table_audit", ROOT / "code/audit_small_tables.py"
    )
    if spec is None or spec.loader is None:
        raise RuntimeError("Cannot load independent table auditor")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)

    tables = []
    for relative, n, digest in (
        ("machines/upstream_zfc_253.tm", 253,
         "84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95"),
        ("machines/upstream_zfc_254.tm", 254,
         "d655ce2cf8cccebd21caa21a49f0f9f010960a44b95c17aae6cc425c518954eb"),
        ("fixed_emission/results/candidate.tm", 283,
         "2e544e7fcb295696fd839d2f8268c799d729f05d95e12cdb3ebef04bfff578a6"),
    ):
        result = module.audit(ROOT / relative)
        result["machine"] = relative
        if result["working_states"] != n or result["sha256"] != digest:
            raise RuntimeError(f"Unexpected table identity: {relative}")
        tables.append(result)

    checks = [
        checked_run(["audit.py"], ROOT / "fixed_emission"),
        checked_run([
            "verify_operation_certificate.py",
            "--reference", "results/reference_dag.json",
            "--candidate", "results/candidate_dag.json",
            "--certificate", "results/rm_bisimulation.json",
        ], ROOT / "fixed_emission"),
        checked_run(["quick_verify.py"], ROOT / "optimizer"),
    ]
    summary = {
        "status": "pass",
        "manifested_files_verified": len(manifest),
        "literal_table_audits": tables,
        "checks": checks,
        "scope": {
            "new_sub_253_consistency_machine_claimed": False,
            "proof_assistant_rebuild": False,
            "full_1272_compilation_search_repeated": False,
            "long_startup_runs_repeated": False,
            "capped_startup_runs_remain_unresolved": True,
        },
    }
    (ROOT / "data/reproduction_result.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n"
    )
    print(json.dumps({
        "status": "pass",
        "manifested_files_verified": len(manifest),
        "working_states": [x["working_states"] for x in tables],
        "check_groups": len(checks),
        "full_report": "data/reproduction_result.json",
        "scope": summary["scope"],
    }, indent=2))


if __name__ == "__main__":
    main()
