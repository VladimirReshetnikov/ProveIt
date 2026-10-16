#!/usr/bin/env python3
"""Offline finite verification for the ProveIt research report.

Run with Python 3.10+ without -O. This does not run Lean/Coq or prove
the halting-equivalence of a newly compiled Turing machine.
"""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def main():
    if not __debug__ or sys.flags.optimize:
        raise SystemExit("Run without -O: diagnostic assertions must be enabled.")
    env = dict(os.environ)
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    results = ROOT / "results"
    results.mkdir(exist_ok=True)
    jobs = [
        ("profile_translation", ROOT,
         ["code/proxy_kernel.py", "--output", "results/proxy_replayed.json"]),
        ("proxy_compiler_replay", ROOT / "experiments/o_erasure",
         ["measure_proxy.py", "--replay"]),
        ("proxy_literal_audit", ROOT / "experiments/o_erasure",
         ["audit_proxy_artifacts.py"]),
        ("literal_quotient_certificate", ROOT / "experiments/record",
         ["verify_certificate.py"]),
        ("macro_witness_census", ROOT / "experiments/record",
         ["macro_census.py"]),
        ("combinatory_compiler_regressions", ROOT / "experiments/sk_carrier",
         ["test_carrier.py"]),
    ]
    summary = {"scope": "Finite checks and complete finite quotient certificate; no new end-to-end consistency-machine proof.", "checks": []}
    for name, cwd, arguments in jobs:
        print(f"Running {name} ...", flush=True)
        proc = subprocess.run([sys.executable, "-B", *arguments], cwd=cwd,
                              env=env, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, text=True)
        log = results / (name + ".log.txt")
        log.write_text(proc.stdout)
        record = {"name": name, "returncode": proc.returncode,
                  "log": str(log.relative_to(ROOT)),
                  "log_sha256": hashlib.sha256(log.read_bytes()).hexdigest()}
        summary["checks"].append(record)
        (results / "reproduction.json").write_text(json.dumps(summary, indent=2) + "\n")
        if proc.returncode:
            print(proc.stdout)
            raise SystemExit(f"FAILED: {name}; see {log}")
        print(f"PASS: {name}", flush=True)
    expected = json.loads((results / "proxy_validation.json").read_text())
    got = json.loads((results / "proxy_replayed.json").read_text())
    if got != expected:
        raise SystemExit("Profile diagnostic output differs from its frozen reference.")
    print("All six verification jobs passed. Scope limitations are in report.pdf.")


if __name__ == "__main__":
    main()
