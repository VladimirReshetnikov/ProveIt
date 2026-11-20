#!/usr/bin/env python3
"""Run all three-dimensional volume checks without modifying the source tree."""
import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent

def run(*command):
    subprocess.run(command, cwd=ROOT, check=True)

def main():
    if not __debug__:
        raise SystemExit("Run under ordinary Python so that certificate assertions are enabled.")
    run(sys.executable, "lower/check_planar.py")
    run(sys.executable, "lower/check_witness.py")
    run(sys.executable, "upper/check_adaptive.py")
    with tempfile.TemporaryDirectory() as temp:
        exe = Path(temp) / "check_rotations"
        run(os.environ.get("CXX", "c++"), "-O3", "-std=c++17",
            "lower/check_rotations.cpp", "-o", str(exe))
        run(str(exe))
    print("The lower and upper estimates both passed.")

if __name__ == "__main__":
    main()
