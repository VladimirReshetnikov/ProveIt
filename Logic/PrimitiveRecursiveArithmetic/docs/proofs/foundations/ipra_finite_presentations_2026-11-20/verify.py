#!/usr/bin/env python3
"""Replay the finite arithmetic tests and, optionally, all Lean modules."""
import argparse
import os
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parent


def run(command, cwd=None):
    print("+", " ".join(str(x) for x in command), flush=True)
    subprocess.run(command, check=True, cwd=cwd)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", action="store_true",
                        help="also check Lean files with the configured Lean 4.32.0")
    parser.add_argument("--proveit", type=Path, metavar="CHECKOUT",
                        help="run Lean in this prepared ProveIt Lake workspace")
    args = parser.parse_args()
    for file in sorted((ROOT / "code").glob("*.py")):
        # Assertions are verification conditions in these programs.
        env = dict(os.environ)
        env.pop("PYTHONOPTIMIZE", None)
        print(f"+ python3 code/{file.name}", flush=True)
        subprocess.run([sys.executable, "-B", str(file)], check=True, env=env)
    if args.lean or args.proveit:
        command = ["lake", "env", "lean"] if args.proveit else ["lean"]
        directory = args.proveit.resolve() if args.proveit else ROOT
        run(command + ["--version"], cwd=directory)
        for file in sorted((ROOT / "lean").glob("*.lean")):
            run(command + [str(file)], cwd=directory)
    print("Every requested check passed.", flush=True)


if __name__ == "__main__":
    main()
