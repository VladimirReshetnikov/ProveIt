#!/usr/bin/env python3
"""Rebuild both papers; optionally regenerate all certificates and figures."""
from pathlib import Path
import argparse
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
PAPERS = ("finite_population_parity", "five_observation_recovery")


def run(argv):
    print("Running:", " ".join(map(str, argv)), flush=True)
    subprocess.run(list(map(str, argv)), cwd=ROOT, check=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true",
                        help="regenerate the exact checks and both figures before compiling")
    args = parser.parse_args()
    if args.check:
        (ROOT / "verification").mkdir(exist_ok=True)
        run([sys.executable, "checks/certify_double_blind.py",
             "verification/double_blind_certificate.json"])
        run([sys.executable, "checks/verify_symbols.py"])
        run([sys.executable, "checks/verify_parity.py"])
        run([sys.executable, "checks/plot_shapes.py"])
    if shutil.which("pdflatex") is None:
        raise SystemExit("pdflatex was not found. Install a TeX distribution first.")
    for paper in PAPERS:
        if shutil.which("latexmk"):
            run(["latexmk", "-pdf", "-silent", "-interaction=nonstopmode",
                 "-halt-on-error", paper + ".tex"])
        else:
            for _ in range(2):
                run(["pdflatex", "-interaction=nonstopmode", "-halt-on-error",
                     paper + ".tex"])
        log = (ROOT / (paper + ".log")).read_text(errors="replace")
        problems = [line for line in log.splitlines()
                    if "Overfull" in line or "undefined" in line.lower()
                    or "Missing character" in line]
        if problems:
            raise SystemExit("Review the TeX log for " + paper + ":\n" + "\n".join(problems))
    print("Both PDFs compiled with no overfull boxes, undefined references, or missing characters.")


if __name__ == "__main__":
    main()
