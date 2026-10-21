#!/usr/bin/env python3
"""Rebuild the concrete ZC215 scheduler proof and recursively check its object.

Standard-library Python and Coq/Rocq's coqc/coqchk commands suffice.  This is
not a proof of the complete binary-machine or ZFC endpoint.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import time


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", type=Path, required=True,
                        help="Fresh output directory for the proof object and logs")
    parser.add_argument("--coqc", default="coqc")
    parser.add_argument("--coqchk", default="coqchk")
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=False)
    source = Path(__file__).resolve().with_name("ConcretePrefixCredit.v")
    destination = args.out / source.name
    shutil.copyfile(source, destination)
    receipt: dict = {
        "source": source.name,
        "sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "scope": "Concrete ZC215 Cantor codec, parser and prefix-credit theorems",
        "complete_binary_or_zfc_endpoint": False,
        "checks": [],
    }
    commands = [
        ("version", [args.coqc, "--version"]),
        ("compile", [args.coqc, "-q", destination.name]),
        ("kernel", [args.coqchk, "-silent", "ConcretePrefixCredit"]),
    ]
    success = True
    for name, command in commands:
        started = time.monotonic()
        result = subprocess.run(command, cwd=args.out, capture_output=True, text=True)
        log = args.out / f"{name}.log"
        log.write_text(result.stdout + result.stderr)
        receipt["checks"].append({
            "name": name, "command": command, "exit_code": result.returncode,
            "elapsed_seconds": round(time.monotonic() - started, 6),
            "log": log.name,
        })
        if result.returncode:
            success = False
            break
        if name == "compile":
            count = result.stdout.count("Closed under the global context")
            receipt["closed_assumption_reports"] = count
            if count != 6 or "Axioms:" in result.stdout:
                success = False
                break
    receipt["success"] = success
    (args.out / "result.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2))
    if not success:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
