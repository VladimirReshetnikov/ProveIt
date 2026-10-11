#!/usr/bin/env python3
"""Reproduce the exact checks and numerical diagnostics in this package."""
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
SCRIPTS = (
    "verify_zero_block_kernel.py",
    "identity_moments_verify.py",
    "identity_generator_verify.py",
    "verify_r8_audit.py",
    "verify_mellin_derivatives.py",
)


def main():
    (HERE.parent / "results").mkdir(exist_ok=True)
    for name in SCRIPTS:
        print("Running " + name, flush=True)
        subprocess.run([sys.executable, str(HERE / name)], check=True,
                       cwd=HERE.parent)
    print("All exact checks and numerical diagnostics passed.", flush=True)


if __name__ == "__main__":
    main()
