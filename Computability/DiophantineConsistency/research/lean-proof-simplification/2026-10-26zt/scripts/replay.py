#!/usr/bin/env python3
"""Focused replay; requires a pinned ProveIt checkout and its Lake environment.

Usage: python3 scripts/replay.py /path/to/ProveIt [--plan-only]
No source patch is applied. Fresh observations go to replay-results/.
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
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
KERNELS = [
    ("SourceGuardRecovery", 2),
    ("SourceGuardClient", 2),
    ("DivisionInterval", 4),
    ("RotationCongruence", 3),
    ("RotationPeriod", 4),
]
PREREQUISITES = [
    "DiophantineConsistency.SplitCertificate59",
    "DiophantineConsistency.NativeCyclicConvolution",
    "DiophantineConsistency.NativeCyclicRotation",
]

def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("repository", type=Path)
    parser.add_argument("--plan-only", action="store_true")
    args = parser.parse_args()
    repo = args.repository.resolve()
    manifest = json.loads((HERE / "evidence/source-manifest.json").read_text())
    for f in manifest["files"]:
        p = repo / f["path"]
        if not p.is_file() or sha(p) != f["sha256"]:
            raise SystemExit("Source identity mismatch: " + f["path"])
    expected = json.loads((HERE / "evidence/packaged-validation.json").read_text())
    for k in expected["kernels"]:
        if sha(HERE / k["file"]) != k["sha256"]:
            raise SystemExit("Packaged kernel identity mismatch: " + k["file"])
    patch_status = []
    for patch in sorted((HERE / "patches").glob("*.patch")):
        r = subprocess.run(["git", "apply", "--check", str(patch)], cwd=repo,
                           text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        patch_status.append({"patch": patch.name, "exit_code": r.returncode, "output": r.stdout})
        if r.returncode:
            raise SystemExit("Patch no longer applies: " + patch.name + "\n" + r.stdout)
    if args.plan_only:
        print(json.dumps({"source_files_verified": len(manifest["files"]),
                          "kernel_files_verified": len(expected["kernels"]),
                          "patches": patch_status,
                          "will_build": PREREQUISITES,
                          "will_check": KERNELS,
                          "source_patches_applied": False}, indent=2))
        return
    out = HERE / "replay-results"
    objects = out / "objects"
    objects.mkdir(parents=True, exist_ok=True)
    records = []
    def run(name, command, env=None, expected_audits=0):
        start = time.monotonic()
        r = subprocess.run(command, cwd=repo, env=env, text=True,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (out / (name + ".log")).write_text(r.stdout)
        record = {"name": name, "command": command, "exit_code": r.returncode,
                  "elapsed_seconds": round(time.monotonic() - start, 3)}
        if expected_audits:
            groups = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", r.stdout, re.S)
            axioms = {x.strip() for g in groups for x in g.split(",") if x.strip()}
            record["axiom_reports"] = len(groups) + r.stdout.count("does not depend on any axioms")
            record["axioms"] = sorted(axioms)
            if record["axiom_reports"] != expected_audits or axioms - ALLOWED_AXIOMS:
                record["audit_error"] = "Missing, unexpected, or nonstandard axiom reports"
        records.append(record)
        (out / "replay.json").write_text(json.dumps(records, indent=2) + "\n")
        print(name + ": exit " + str(r.returncode), flush=True)
        if r.returncode or record.get("audit_error"):
            raise SystemExit("Replay failed; inspect " + str(out / (name + ".log")))
        return r.stdout
    version = run("lean-version", ["lake", "env", "lean", "--version"])
    if "version 4.32.0," not in version:
        raise SystemExit("Expected Lean 4.32.0")
    run("focused-prerequisites", ["lake", "build"] + PREREQUISITES)
    # Read only the executable and module search path, not unrelated environment secrets.
    setup = subprocess.check_output([
        "lake", "env", sys.executable, "-c",
        "import json,os,shutil; print(json.dumps({'lean':shutil.which('lean'),"
        "'lean_path':os.environ.get('LEAN_PATH','')}))"
    ], cwd=repo, text=True)
    state = json.loads(setup)
    if not state["lean"]:
        raise SystemExit("Lake did not locate Lean")
    env = os.environ.copy()
    env["LEAN_PATH"] = str(objects) + os.pathsep + state["lean_path"]
    for name, audits in KERNELS:
        run(name, [state["lean"], "--root=" + str(HERE / "lean"),
                   str(HERE / "lean" / (name + ".lean")),
                   "-o", str(objects / (name + ".olean"))],
            env=env, expected_audits=audits)
    print("Focused replay passed. Candidate production patches were not applied or fully built.")

if __name__ == "__main__":
    main()
