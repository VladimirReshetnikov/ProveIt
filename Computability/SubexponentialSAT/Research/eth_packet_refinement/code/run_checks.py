#!/usr/bin/env python3
"""Reproduce the new finite checks sequentially using the current Python."""

from pathlib import Path
import subprocess
import sys


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    tasks = [
        (False, "verify_packing.py", "packing_checks.json"),
        (True, "verify_packing.py", "packing_checks_optimized.json"),
        (False, "verify_schedule.py", "schedule_verification.json"),
        (True, "verify_schedule.py", "schedule_verification_optimized.json"),
    ]
    for optimized, script, output in tasks:
        command = [sys.executable]
        if optimized:
            command.append("-O")
        command.extend([str(root / "code" / script), "--output",
                        str(root / "results" / output)])
        subprocess.run(command, cwd=root, check=True)
    print("All packing and schedule checks passed in normal and optimized Python.")


if __name__ == "__main__":
    main()
