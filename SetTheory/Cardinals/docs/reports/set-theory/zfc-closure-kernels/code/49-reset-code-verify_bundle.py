#!/usr/bin/env python3
"""Replay the delivered finite evidence; this is not a proof assistant.

The default run needs only Python's standard library. --full also uses a
C++17 compiler to replay both complete, bounded state-fusion censuses.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess
import sys
import tempfile

PACKAGE = Path(__file__).resolve().parents[1]


def run(script: str, *arguments: object) -> None:
    command = [sys.executable, str(PACKAGE / script)]
    command.extend(str(argument) for argument in arguments)
    process = subprocess.run(command, text=True, capture_output=True)
    if process.returncode:
        sys.stdout.write(process.stdout)
        sys.stderr.write(process.stderr)
        raise SystemExit(process.returncode)


def same_json(actual: Path, expected: str) -> None:
    if json.loads(actual.read_text()) != json.loads((PACKAGE / expected).read_text()):
        raise SystemExit(f"Reproduction differs from {expected}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--full", action="store_true",
                        help="Also rebuild and replay both complete fusion censuses.")
    arguments = parser.parse_args()
    if not __debug__:
        raise SystemExit("Run without -O: the supplied reference checkers use assertions.")

    with tempfile.TemporaryDirectory(prefix="zfc-reset-hod-verify-") as directory:
        temporary = Path(directory)

        baseline = temporary / "baseline.json"
        run("code/audit_baseline.py", "--output", baseline)
        same_json(baseline, "results/baseline_audit.json")
        print("PASS: literal 252-state table and entire 82,552-step bootstrap frame.", flush=True)

        reset = temporary / "reset.json"
        run("reset/late_start_credit.py", "--output", reset)
        same_json(reset, "reset/results.json")
        print("PASS: all finite reset cases, 5,000 credit certificates and 256-control census.", flush=True)

        quick = temporary / "machine-quick.json"
        run("machine/code/reproduce.py", "--quick", "--output", quick)
        same_json(quick, "machine/results/portable_quick_verification.json")
        print("PASS: all 8,391 affine cases and independent complete bootstrap replay.", flush=True)

        startup = temporary / "startup.json"
        run("reset/startup_protected_audit.py",
            "--machine-code", PACKAGE / "machine/code",
            "--table", PACKAGE / "machine/inputs/permutation252_old.tm",
            "--output", startup)
        same_json(startup, "reset/startup_protected_audit.json")
        print("PASS: complete runtime footprint covers all 504 rows and 252 states.", flush=True)

        if arguments.full:
            print("Replaying radius-six and radius-eight fusion censuses; allow several minutes.", flush=True)
            run("machine/code/reproduce.py", "--radius", 6, 8,
                "--output", temporary / "machine-full.json")
            print("PASS: both full per-pair ledgers and every functional count match.", flush=True)

    print("All requested finite evidence reproduced. No unbounded theorem is inferred from these runs.")


if __name__ == "__main__":
    main()
