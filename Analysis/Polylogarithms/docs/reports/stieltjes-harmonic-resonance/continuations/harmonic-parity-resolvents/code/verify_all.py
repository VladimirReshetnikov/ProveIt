#!/usr/bin/env python3
"""Run the independent verification scripts; preserve original delivered records."""
from __future__ import annotations

import argparse
import json
import platform
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CODE = ROOT / "code"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--full", action="store_true",
                        help="Also rerun slow direct Stieltjes, Lerch, and Tornheim diagnostics.")
    parser.add_argument("--output-dir", type=Path, default=ROOT / "results/latest")
    args = parser.parse_args()
    out = args.output_dir.resolve()
    out.mkdir(parents=True, exist_ok=True)
    jobs = [
        ("harmonic_parity", ["verify_harmonic_parity.py", "--output",
                            str(out / "harmonic_parity_checks.json")]),
        ("resolvent_contact", ["verify_resolvent_contact.py", "--output",
                              str(out / "resolvent_contact_checks.json")]),
        ("harmonic_reduction", ["verify_harmonic.py", "--out",
                               str(out / "harmonic_verification.json")]
         + ([] if args.full else ["--exact-only"])),
        ("quartic_tornheim", ["check_quartic_tornheim.py", "--output",
                             str(out / "quartic_tornheim_checks.json")]
         + (["--numeric"] if args.full else [])),
        ("resolvent", ["verify_resolvent.py", "--output",
                      str(out / "resolvent_checks.json"), "--progress"]
         + (["--full"] if args.full else [])),
    ]
    records = []
    for name, arguments in jobs:
        print(f"Running {name}...", flush=True)
        started = time.monotonic()
        command = [sys.executable, str(CODE / arguments[0]), *arguments[1:]]
        result = subprocess.run(command, cwd=ROOT, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (out / (name + ".log")).write_text(result.stdout)
        records.append({"name": name, "returncode": result.returncode,
                        "seconds": round(time.monotonic() - started, 3)})
        print(f"{name}: {'passed' if result.returncode == 0 else 'FAILED'}", flush=True)
        if result.returncode:
            print(result.stdout[-6000:])
            break
    summary = {
        "mode": "full" if args.full else "routine",
        "python": platform.python_version(),
        "status": "passed" if len(records) == len(jobs)
                  and all(x["returncode"] == 0 for x in records) else "failed",
        "jobs": records,
        "qualification": "Exact finite checks and floating-point diagnostics; no interval certificates."
    }
    (out / "run_summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))
    if summary["status"] != "passed":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
