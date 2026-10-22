#!/usr/bin/env python3
"""Run the packet's focused checks serially; never edit the input repository."""
import argparse
from pathlib import Path
import shutil
import subprocess
import sys

def main():
    here = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", required=True, type=Path)
    parser.add_argument("--lean", required=True)
    parser.add_argument("--output", type=Path, default=here / "verification-run")
    args = parser.parse_args()
    lean = shutil.which(args.lean) or args.lean
    lean = str(Path(lean).resolve())
    repo = str(args.repo.resolve())
    output = args.output.resolve()
    commands = [
        [sys.executable, str(here / "shared-implication/verify_refactor.py"),
         "--repo", repo, "--lean", lean,
         "--countermodel", str(here / "countermodel/DiagonalCountermodel.lean"),
         "--output", str(output / "core")],
        [sys.executable, str(here / "semantic-sites/verify.py"),
         "--repo", repo, "--lean", lean, "--build", str(output / "sites")],
        [sys.executable, str(here / "countermodel/check_countermodel.py")]
    ]
    for command in commands:
        subprocess.run(command, check=True)
    print("PASS: focused core, countermodel, and semantic-site checks.")
    print("The full K215 endpoint and Rocq draft are outside this verification scope.")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())

