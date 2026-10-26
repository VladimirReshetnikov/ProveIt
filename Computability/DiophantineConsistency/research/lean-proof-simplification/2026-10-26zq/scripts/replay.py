#!/usr/bin/env python3
"""Replay the focused Lean evidence without applying a repository patch.

Usage: python3 scripts/replay.py /path/to/ProveIt [--plan-only]
Requires the pinned repository, its Lake toolchain, and Python 3.
Outputs go into replay-results/, never into the packaged original receipts.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent.parent
PIN = "9f35798db4a63c25e435fca14d75931144657d7e"
REFRESH = "f00ba53b331833c6cb64707bd90e48489e5610f5"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
PROTOTYPES = [
    "RestrictedSubsetSums", "SubsetTranslation", "FixedPeriods",
    "ResidueTower", "LiftSeed", "PrimePowerAnnihilator", "AffineSubsetCoverage",
]
PREREQUISITES = [
    "DiophantineConsistency.ControllerResidueLift",
    "DiophantineConsistency.PrimePowerOrder",
]


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def checked_output(args: list[str], cwd: Path) -> str:
    return subprocess.check_output(args, cwd=cwd, text=True).strip()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("repository", type=Path)
    parser.add_argument("--plan-only", action="store_true",
                        help="verify all source hashes and list checks without invoking Lake")
    args = parser.parse_args()
    repo = args.repository.resolve()
    head = checked_output(["git", "rev-parse", "HEAD"], repo)
    if head not in {PIN, REFRESH}:
        raise SystemExit(f"Expected checked baseline {PIN} or verified unchanged refresh {REFRESH}; found {head}.")
    manifest = json.loads((HERE / "evidence/source_manifest.json").read_text())
    for entry in manifest["files"]:
        source = repo / entry["path"]
        if not source.is_file() or digest(source) != entry["sha256"]:
            raise SystemExit(f"Baseline source mismatch: {entry['path']}")
    original = json.loads((HERE / "evidence/validation.json").read_text())
    for record in original["prototypes"]:
        if digest(HERE / record["file"]) != record["source_sha256"]:
            raise SystemExit(f"Packaged proof source mismatch: {record['file']}")
    patch = HERE / "patches/prime-power-annihilator.patch"
    subprocess.run(["git", "apply", "--check", str(patch)], cwd=repo, check=True)
    if args.plan_only:
        print(json.dumps({"baseline": head, "verified_source_files": len(manifest["files"]),
                          "prerequisites": PREREQUISITES, "prototypes": PROTOTYPES,
                          "refactor": "PrimePowerOrder plus unchanged PrimePowerOrderChecks",
                          "patch_applies": True, "patch_will_be_applied": False}, indent=2))
        return

    out = HERE / "replay-results"
    out.mkdir(exist_ok=True)
    records: list[dict] = []

    def run(name: str, command: list[str], *, env: dict | None = None,
            audit: bool = False) -> str:
        start = time.monotonic()
        result = subprocess.run(command, cwd=repo, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (out / f"{name}.log").write_text(result.stdout)
        record = {"name": name, "command": command, "exit_code": result.returncode,
                  "elapsed_seconds": round(time.monotonic() - start, 3)}
        if audit:
            groups = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", result.stdout, re.S)
            axioms = {a.strip() for group in groups for a in group.split(",") if a.strip()}
            record["axioms"] = sorted(axioms)
            record["axiom_reports"] = len(groups) + result.stdout.count("does not depend on any axioms")
        records.append(record)
        (out / "replay.json").write_text(json.dumps(records, indent=2) + "\n")
        print(f"{name}: exit {result.returncode}", flush=True)
        if result.returncode:
            raise SystemExit(f"Check failed; see {out / (name + '.log')}")
        if audit and (not record["axiom_reports"] or set(record["axioms"]) - ALLOWED_AXIOMS):
            raise SystemExit(f"Missing or nonstandard axiom audit in {name}.")
        return result.stdout

    version = run("lean-version", ["lake", "env", "lean", "--version"])
    if "version 4.32.0," not in version:
        raise SystemExit("The requested replay uses Lean 4.32.0.")
    run("focused-prerequisites", ["lake", "build", *PREREQUISITES])
    mathlib_head = checked_output(["git", "-C", str(repo / ".lake/packages/mathlib"),
                                   "rev-parse", "HEAD"], repo)
    if mathlib_head != manifest["mathlib_commit"]:
        raise SystemExit(f"Unexpected mathlib revision: {mathlib_head}")

    # Ask Lake for its actual environment through this same Python executable.
    # This works without shell-specific commands such as `printenv` or `which`.
    environment_code = (
        "import json,os,shutil; "
        "print(json.dumps({'env':dict(os.environ),'lean':shutil.which('lean')}))"
    )
    lake_state = json.loads(checked_output(
        ["lake", "env", sys.executable, "-c", environment_code], repo))
    if not lake_state["lean"]:
        raise SystemExit("Lake did not resolve its Lean executable.")
    lean = lake_state["lean"]
    objects = out / "objects"
    objects.mkdir(exist_ok=True)
    base_env = lake_state["env"]
    env = dict(base_env)
    env["LEAN_PATH"] = str(objects) + os.pathsep + base_env.get("LEAN_PATH", "")
    for name in PROTOTYPES:
        source = HERE / "lean" / f"{name}.lean"
        run(name, [lean, f"--root={HERE / 'lean'}", str(source),
                   "-o", str(objects / f"{name}.olean")], env=env, audit=True)

    # A second, higher-priority object directory shadows precisely one module.
    # No source in the user's repository is changed.
    refactored = out / "refactored"
    (refactored / "DiophantineConsistency").mkdir(parents=True, exist_ok=True)
    ref_env = dict(env)
    ref_env["LEAN_PATH"] = str(refactored) + os.pathsep + env["LEAN_PATH"]
    source = HERE / "replacement/DiophantineConsistency/PrimePowerOrder.lean"
    run("PrimePowerOrderRefactored", [lean, f"--root={HERE / 'replacement'}", str(source),
         "-o", str(refactored / "DiophantineConsistency/PrimePowerOrder.olean")], env=ref_env)
    checks = repo / "Computability/DiophantineConsistency/Lean/DiophantineConsistency/PrimePowerOrderChecks.lean"
    run("PrimePowerOrderChecks", [lean, str(checks)], env=ref_env, audit=True)
    print("All focused checks passed. No patch was applied and no tracked source was changed.")


if __name__ == "__main__":
    main()
