#!/usr/bin/env python3
"""Replay the six independent verification programs; retain concise logs.

Run: python verification/run_checks.py
Requires sympy and mpmath, at versions stated in requirements.txt.
The numerical checks may take several minutes. They are diagnostics,
not interval proofs. Mathematical proofs are in the article.
"""
from pathlib import Path
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
PROGRAMS = ["verify_reconstruction.py", "verify_reconstruction_cutoffs.py",
            "verify_rank_eight.py", "verify_centered_cubic.py",
            "verify_second_resonance.py", "verify_spectral_mellin.py"]


def main():
    logs = HERE/"replay_logs"
    logs.mkdir(exist_ok=True)
    for name in PROGRAMS:
        print("Running", name, flush=True)
        start = time.monotonic()
        with (logs/(Path(name).stem+".txt")).open("w", encoding="utf-8") as log:
            result = subprocess.run([sys.executable, str(HERE/name)], cwd=HERE,
                                    stdout=log, stderr=subprocess.STDOUT)
        if result.returncode:
            raise SystemExit(f"{name} failed; inspect {logs/(Path(name).stem+'.txt')}")
        print(f"Passed in {time.monotonic()-start:.1f} seconds", flush=True)
    print("All six verification programs completed successfully.")


if __name__ == "__main__":
    main()
