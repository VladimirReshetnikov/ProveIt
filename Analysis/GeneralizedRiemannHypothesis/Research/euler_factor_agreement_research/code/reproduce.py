#!/usr/bin/env python3
"""Run the exact checks and rebuild both papers from the archive root.

Checks require Python 3 standard library only. PDF builds require pdfLaTeX
with the packages listed in the TeX preambles. Optional figure regeneration
requires NumPy and Matplotlib. No network access is used.
"""
from pathlib import Path
import argparse
import json
import os
import shutil
import subprocess
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--checks-only", action="store_true")
    parser.add_argument("--regenerate-figure", action="store_true")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    results = root / "results"
    results.mkdir(exist_ok=True)
    report = {"status": "PASS", "checks": [], "pdf_builds": []}
    for script in ("verify_exact.py", "verify_field.py", "verify_rajan_family.py"):
        run = subprocess.run([sys.executable, str(root / "code" / script)],
                             cwd=root, text=True, capture_output=True)
        if run.returncode:
            sys.stderr.write(run.stdout + run.stderr)
            raise SystemExit(f"FAILED: {script}")
        data = json.loads(run.stdout)
        if data.get("status") != "PASS":
            raise SystemExit(f"Missing PASS status: {script}")
        report["checks"].append({"script": script, "status": "PASS"})
        print(f"PASS {script}", flush=True)
    if args.regenerate_figure:
        subprocess.run([sys.executable, str(root / "code" / "make_figure.py")],
                       cwd=root, check=True)
        print("Regenerated the trace-triangle figure.", flush=True)
    if not args.checks_only:
        if not shutil.which("pdflatex"):
            raise SystemExit("pdfLaTeX is required for PDF builds; use --checks-only for the exact arithmetic checks.")
        env = dict(os.environ)
        env["SOURCE_DATE_EPOCH"] = "1795737600"  # 2026-11-27 00:00 UTC.
        env["FORCE_SOURCE_DATE"] = "1"
        for name in ("rajan_counterexample", "cubic_euler_agreement"):
            for pass_number in (1, 2):
                run = subprocess.run(
                    ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", name+".tex"],
                    cwd=root, env=env, text=True, capture_output=True)
                log = run.stdout + run.stderr
                (results / f"{name}_latex_pass{pass_number}.txt").write_text(log)
                if run.returncode:
                    sys.stderr.write(log[-8000:])
                    raise SystemExit(f"PDF build failed: {name}, pass {pass_number}")
            overfull = [line for line in log.splitlines() if "Overfull" in line]
            unresolved = [line for line in log.splitlines()
                          if "undefined" in line.lower() or "Rerun to get" in line]
            if overfull or unresolved:
                raise SystemExit(f"Layout or reference check failed in {name}: {overfull + unresolved}")
            report["pdf_builds"].append({"name": name, "passes": 2,
                                         "overfull_boxes": 0, "unresolved_references": 0})
            print(f"PASS {name}.pdf (two passes; no overfull boxes or unresolved references)", flush=True)
    (results / "build_validation.json").write_text(json.dumps(report, indent=2)+"\n")


if __name__ == "__main__":
    main()
