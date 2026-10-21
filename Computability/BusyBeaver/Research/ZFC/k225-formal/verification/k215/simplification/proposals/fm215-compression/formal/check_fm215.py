#!/usr/bin/env python3
"""Sequentially kernel-check the FM215 proof and its exact literal inputs.

Usage: python3 check_fm215.py --lean /path/to/lean
Requires the official Lean 4.32.0 toolchain; no project dependencies.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", default="lean")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    version = subprocess.check_output([args.lean, "--version"], text=True).strip()
    if not version.startswith("Lean (version 4.32.0,"):
        raise SystemExit("This receipt pins Lean 4.32.0; observed: " + version)
    env = os.environ.copy()
    env["LEAN_PATH"] = str(root) + (":" + env["LEAN_PATH"] if env.get("LEAN_PATH") else "")
    receipt = {"status": "IN_PROGRESS", "compiler": version, "modules": []}
    receipt_path = root / "fm215-kernel-receipt.json"
    for name in ("PositiveSimulation", "FM215Data", "FM215"):
        source = root / (name + ".lean")
        target = root / (name + ".olean")
        started = time.monotonic()
        proc = subprocess.run([args.lean, "-o", str(target), str(source)],
                              cwd=root, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        log = root / (name + ".compile.log")
        log.write_text(proc.stdout)
        result = {
            "module": name, "exit_code": proc.returncode,
            "seconds": round(time.monotonic() - started, 3),
            "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
            "log_sha256": hashlib.sha256(log.read_bytes()).hexdigest(),
            "output": proc.stdout,
        }
        if proc.returncode == 0:
            result["olean_sha256"] = hashlib.sha256(target.read_bytes()).hexdigest()
        receipt["modules"].append(result)
        receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")
        print(name + ": " + ("PASS" if proc.returncode == 0 else "FAIL"), flush=True)
        print(proc.stdout, end="", flush=True)
        if proc.returncode:
            receipt["status"] = "FAIL_COMPILER"
            receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")
            raise SystemExit(proc.returncode)
    bindings = subprocess.run([sys.executable, str(root / "check_lean_bindings.py"),
                               "--output", str(root / "lean-bindings.json")],
                              cwd=root, text=True, capture_output=True)
    print(bindings.stdout, end="")
    print(bindings.stderr, end="", file=sys.stderr)
    receipt["binding_check_exit_code"] = bindings.returncode
    receipt["status"] = "PASS_KERNEL_AND_EXACT_BINDINGS" if bindings.returncode == 0 else "FAIL_BINDINGS"
    receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")
    raise SystemExit(bindings.returncode)


if __name__ == "__main__":
    main()
