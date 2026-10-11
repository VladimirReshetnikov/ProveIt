#!/usr/bin/env python3
"""Replay every distributed mathematical check using the active Python runtime.

Run from any directory. The article contains the analytic proofs. Numerical
comparisons here are diagnostics, not interval certificates or formal proofs.
"""
from __future__ import annotations
from datetime import datetime, timezone
import hashlib
import importlib.metadata
import json
from pathlib import Path
import platform
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
SUITES = [
    ("order8", "order8/verify_order8_completion.py", []),
    ("general_normalization", "eventual/verify_general_normalization.py", []),
    ("eventual_thresholds", "eventual/eventual_threshold.py", ["1", "2", "3", "4", "5"]),
    ("order8_identity", "order8/reconstruct_order8.py", []),
    ("quartic", "quartic/verify_quartic.py", []),
    ("bilateral", "bilateral/verify_spectral_defects.py", []),
    ("one_sided", "one_sided/verify_stieltjes_jets.py", []),
]


def main():
    logs = ROOT / "logs"
    logs.mkdir(exist_ok=True)
    receipt = {
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "python": sys.version,
        "platform": platform.platform(),
        "versions": {name: importlib.metadata.version(name)
                     for name in ("sympy", "mpmath")},
        "scope": "Exact finite checks plus separate non-interval numerical diagnostics.",
        "suites": [],
    }
    for name, relative, args in SUITES:
        path = ROOT / relative
        start = time.monotonic()
        print(f"Running {relative}", flush=True)
        with (logs / (name + ".log")).open("w") as output:
            result = subprocess.run([sys.executable, str(path), *args], cwd=path.parent,
                                    stdout=output, stderr=subprocess.STDOUT)
        receipt["suites"].append({
            "suite": name, "script": relative, "arguments": args,
            "script_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "exit_code": result.returncode,
            "seconds": round(time.monotonic() - start, 3),
        })
        print(f"{name}: exit {result.returncode}", flush=True)
        if result.returncode:
            break
    receipt["all_passed"] = (len(receipt["suites"]) == len(SUITES)
                             and all(s["exit_code"] == 0 for s in receipt["suites"]))
    receipt["finished_utc"] = datetime.now(timezone.utc).isoformat()
    (ROOT / "replay_receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    if not receipt["all_passed"]:
        raise SystemExit("A suite failed; inspect verification/logs and replay_receipt.json.")
    print("All distributed mathematical suites passed.")


if __name__ == "__main__":
    main()
