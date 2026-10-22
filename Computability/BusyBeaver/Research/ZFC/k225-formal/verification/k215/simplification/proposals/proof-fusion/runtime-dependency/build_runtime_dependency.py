#!/usr/bin/env python3
"""Compile the pinned production dependencies and the proposed transport module."""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

HERE = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--repo", type=Path, required=True, help="Path to the pinned ProveIt checkout")
parser.add_argument("--lean", default="lean", help="Lean 4.32.0 executable")
parser.add_argument("--out", type=Path, required=True, help="Separate object/log directory")
args = parser.parse_args()
REPO = args.repo.resolve()
LEAN_ROOT = REPO / "Computability/BusyBeaver/Lean"
LEAN = args.lean
DEPS = ["KZip", "KRuntimeCore", "KHome", "FramedWindow", "KZipTape", "KHomeReady"]
BUILD = args.out.resolve()
OUT = BUILD / "BusyBeaver/ZFC"
LOG = BUILD / "logs"
OUT.mkdir(parents=True, exist_ok=True)
LOG.mkdir(parents=True, exist_ok=True)
env = dict(os.environ, LEAN_PATH=str(BUILD), LEAN_NUM_THREADS="1")
commit = subprocess.check_output(["git", "-C", str(REPO), "rev-parse", "HEAD"], text=True).strip()
receipt = {"repo_commit": commit, "sources": []}
if commit != "6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95":
    raise SystemExit("This experiment is pinned to ProveIt commit 6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95")
with open("/tmp/proveit-k215-proof-build.lock", "a") as lock:
    fcntl.flock(lock, fcntl.LOCK_EX)
    receipt["compiler"] = subprocess.check_output([LEAN, "--version"], text=True).strip()
    if "version 4.32.0," not in receipt["compiler"]:
        raise SystemExit("Expected Lean 4.32.0")
    for name in DEPS + ["KRuntimeDependency", "KRuntimeDependencyAudit"]:
        base = HERE if name.startswith("KRuntimeDependency") else LEAN_ROOT
        src = base / "BusyBeaver/ZFC" / (name + ".lean")
        before = src.read_bytes()
        obj = OUT / (name + ".olean")
        cmd = [LEAN, "-j", "1", "-M", "4096", "-R", str(base), "-o", str(obj), str(src)]
        start = time.monotonic()
        cp = subprocess.run(cmd, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, env=env, timeout=240)
        log = LOG / (name + ".log")
        log.write_text(cp.stdout)
        if src.read_bytes() != before:
            raise SystemExit(f"Source changed during compilation: {src}")
        row = {"module": name, "source": str(src), "sha256": hashlib.sha256(before).hexdigest(), "exit_code": cp.returncode, "seconds": round(time.monotonic()-start, 3), "log": str(log), "log_sha256": hashlib.sha256(log.read_bytes()).hexdigest(), "command": cmd}
        if cp.returncode == 0:
            row["object_sha256"] = hashlib.sha256(obj.read_bytes()).hexdigest()
        receipt["sources"].append(row)
        (BUILD / "build_receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
        print(name, cp.returncode, row["seconds"], flush=True)
        if cp.returncode or "sorryAx" in cp.stdout:
            print(cp.stdout, flush=True)
            raise SystemExit(cp.returncode or 1)
receipt["status"] = "PASS"
(BUILD / "build_receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
