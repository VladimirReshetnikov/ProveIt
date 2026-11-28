#!/usr/bin/env python3
"""Rebuild both research papers; optionally rerun their verification scripts."""
from pathlib import Path
import argparse
import os
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
PAPERS = ("spectral_quantile_transition", "symplectic_precision")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify", action="store_true",
                        help="Recompute checks, data, and figures before compiling.")
    args = parser.parse_args()
    if not shutil.which("pdflatex"):
        raise SystemExit("pdflatex was not found; install a LaTeX distribution first.")
    env = os.environ.copy()
    env.setdefault("MPLBACKEND", "Agg")
    for name in PAPERS:
        directory = ROOT / name
        if args.verify:
            print(f"Verifying {name}...", flush=True)
            subprocess.run([sys.executable, str(directory / "code" / "verify.py")],
                           cwd=directory, env=env, check=True)
        build = directory / "build"
        build.mkdir(exist_ok=True)
        command = ["pdflatex", "-interaction=nonstopmode", "-halt-on-error",
                   "-output-directory=build", f"{name}.tex"]
        for run in (1, 2, 3):
            log = build / f"compile-{run}.txt"
            print(f"Compiling {name}, pass {run}...", flush=True)
            with log.open("w") as handle:
                result = subprocess.run(command, cwd=directory, env=env,
                                        stdout=handle, stderr=subprocess.STDOUT)
            if result.returncode:
                raise SystemExit(f"LaTeX failed; see {log}")
        target = directory / f"{name}.pdf"
        shutil.copy2(build / target.name, target)
        print(f"Built {target.relative_to(ROOT)}", flush=True)


if __name__ == "__main__":
    main()
