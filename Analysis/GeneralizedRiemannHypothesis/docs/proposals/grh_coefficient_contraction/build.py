#!/usr/bin/env python3
"""Rebuild the report and exact finite checks; optionally audit a pinned checkout.

This script never runs Lean or modifies the ProveIt checkout.
"""
import argparse
from datetime import datetime
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, help="Optional ProveIt checkout at the pinned commit")
    parser.add_argument("--supplemental", action="store_true",
                        help="Also verify the later proposal cutoff from Git objects (requires --repo)")
    parser.add_argument("--skip-pdf", action="store_true")
    args = parser.parse_args()
    if args.supplemental and not args.repo:
        parser.error("--supplemental requires --repo")
    root = Path(__file__).resolve().parent
    checks = root / "checks"
    jobs = [("check_initial_average.py", "initial_average_results.json", [])]
    if args.repo:
        repo = str(args.repo.resolve())
        jobs.extend([("check_source_audit.py", "source_audit_result.json", [repo]),
                     ("check_proposal_manifest.py", "proposal_audit_result.json", [repo])])
        if args.supplemental:
            jobs.append(("check_supplemental_audit.py", "supplemental_audit_result.json", [repo]))
    for script, output, extra in jobs:
        proc = subprocess.run([sys.executable, str(checks / script), *extra],
                              check=True, text=True, capture_output=True, cwd=root)
        parsed = json.loads(proc.stdout)
        (checks / output).write_text(json.dumps(parsed, indent=2) + "\n")
        print(f"Passed: {script}", flush=True)
    if not args.skip_pdf:
        build = root / ".build"
        build.mkdir(exist_ok=True)
        env = os.environ.copy()
        env["SOURCE_DATE_EPOCH"] = str(int(datetime.fromisoformat(
            "2026-11-28T03:32:11+00:00").timestamp()))
        env["FORCE_SOURCE_DATE"] = "1"
        command = ["pdflatex", "-interaction=nonstopmode", "-halt-on-error",
                   f"-output-directory={build}", "report.tex"]
        for number in range(1, 4):
            proc = subprocess.run(command, text=True, capture_output=True, cwd=root, env=env)
            (build / f"pass{number}.log").write_text(proc.stdout + proc.stderr)
            if proc.returncode:
                print(proc.stdout[-5000:], file=sys.stderr)
                raise SystemExit(proc.returncode)
        final_log = (build / "pass3.log").read_text()
        warnings = [line for line in final_log.splitlines()
                    if "Overfull" in line or "undefined" in line.lower() or
                    "LaTeX Warning:" in line]
        if warnings:
            print("PDF warnings require review:\n" + "\n".join(warnings), file=sys.stderr)
            raise SystemExit(1)
        shutil.copy2(build / "report.pdf", root / "report.pdf")
        print("Built: report.pdf (three passes; no overfull or unresolved-reference warnings)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
