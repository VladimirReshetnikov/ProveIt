#!/usr/bin/env python3
"""Compile the papers; optionally reproduce all supplied verification records."""
from pathlib import Path
import argparse
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
PAPERS = [
    Path("01_endpoint_filters/paper.tex"),
    Path("02_psl2_detectors/psl2_detector.tex"),
    Path("03_sparse_padic/sparse_padic_jump.tex"),
    Path("04_mirror_hessian/paper.tex"),
    Path("research_report.tex"),
]
CHECKS = [
    ("01_endpoint_filters", "verify.py", []),
    ("02_psl2_detectors", "verify_psl2.py", []),
    ("03_sparse_padic", "new_phase_checks.py", ["--large"]),
    ("04_mirror_hessian", "verify_mirror_hessian.py", []),
]

def compile_paper(path):
    source = ROOT / path
    print(f"Compiling {path}", flush=True)
    for run in (1, 2, 3, 4):
        result = subprocess.run(
            ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", source.name],
            cwd=source.parent, text=True, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
        )
        if result.returncode:
            print(result.stdout)
            raise SystemExit(result.returncode)
        if run >= 2 and "Rerun" not in result.stdout and "Label(s) may have changed" not in result.stdout:
            break
    else:
        raise SystemExit(f"References did not stabilize after four runs: {path}")
    print(f"  Created {source.with_suffix('.pdf').relative_to(ROOT)}", flush=True)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--checks", action="store_true", help="also rerun all checks (sparse scan can take minutes)")
    parser.add_argument("--checks-only", action="store_true", help="run checks without compiling PDFs")
    args = parser.parse_args()
    if args.checks or args.checks_only:
        for folder, script, extra in CHECKS:
            print(f"Checking {folder}/{script}", flush=True)
            result = subprocess.run([sys.executable, script, *extra], cwd=ROOT/folder,
                                    text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            (ROOT/folder/"verification_run.txt").write_text(result.stdout)
            if result.returncode:
                print(result.stdout)
                raise SystemExit(result.returncode)
            print("  PASS; output in verification_run.txt", flush=True)
    if not args.checks_only:
        for paper in PAPERS:
            compile_paper(paper)
    print("Done.")

if __name__ == "__main__":
    main()
