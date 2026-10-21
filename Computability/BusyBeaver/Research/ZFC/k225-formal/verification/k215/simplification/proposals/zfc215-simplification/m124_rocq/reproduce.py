#!/usr/bin/env python3
"""Rebuild the three standalone Rocq modules in a fresh output directory."""
from pathlib import Path
import argparse
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent
MODULES = ["M124Table", "M124Facts", "M124Transfer"]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--output", type=Path)
    ap.add_argument("--coqc", default="coqc")
    ap.add_argument("--coqchk", default="coqchk")
    args = ap.parse_args()
    out = args.output.resolve() if args.output else Path(tempfile.mkdtemp(prefix="m124-proof-"))
    if args.output:
        out.mkdir(parents=True, exist_ok=False)
    run = subprocess.run([sys.executable, "-B", str(ROOT / "check_inputs.py")],
                         text=True, capture_output=True)
    (out / "input-check.log").write_text(run.stdout + run.stderr)
    run.check_returncode()
    sources = {}
    for name in MODULES:
        src = ROOT / (name + ".v")
        shutil.copyfile(src, out / src.name)
        sources[src.name] = hashlib.sha256(src.read_bytes()).hexdigest()
    version = subprocess.run([args.coqc, "--version"], text=True,
                             capture_output=True, check=True).stdout.strip()
    entries = []
    for name in MODULES:
        start = time.monotonic()
        p = subprocess.run([args.coqc, name + ".v"], cwd=out,
                           text=True, capture_output=True)
        transcript = p.stdout + p.stderr
        (out / (name + ".log")).write_text(transcript)
        entries.append({"module": name, "exit_code": p.returncode,
                        "seconds": time.monotonic() - start})
        p.check_returncode()
        if name == "M124Transfer":
            assert transcript.count("Closed under the global context") == 3
            assert "Axioms:" not in transcript
    start = time.monotonic()
    p = subprocess.run([args.coqchk, "-silent", "M124Transfer"], cwd=out,
                       text=True, capture_output=True)
    (out / "coqchk.log").write_text(p.stdout + p.stderr)
    p.check_returncode()
    receipt = {"status": "PASS_CLOSED_KERNEL", "version": version,
               "source_sha256": sources, "modules": entries,
               "closed_assumption_reports": 3, "coqchk_exit_code": p.returncode,
               "coqchk_seconds": time.monotonic() - start,
               "scope": "Standalone exact-table all-tape halting equivalence; "
                        "upstream ZFC endpoint model adapter is not yet integrated."}
    (out / "build-receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({"output": str(out), **receipt}, indent=2))


if __name__ == "__main__":
    main()
