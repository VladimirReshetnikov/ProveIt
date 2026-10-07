#!/usr/bin/env python3
"""Run the three exact mathematical verifiers from any working directory."""
from pathlib import Path
import subprocess
import sys


def main() -> None:
    if not __debug__:
        raise SystemExit("Run without -O or -OO; exact verification must retain assertions.")
    root = Path(__file__).resolve().parents[1]
    commands = [
        ["code/verify_energy.py", "--output", "data/energy_checks.json"],
        ["code/verify_cosets.py"],
        ["code/verify_u4.py", "--json", "certificates/u4_certificate.json"],
    ]
    for command in commands:
        print("Running " + " ".join(command), flush=True)
        subprocess.run([sys.executable, *command], cwd=root, check=True)
    print("All packaged exact mathematical verifiers passed.")


if __name__ == "__main__":
    main()
