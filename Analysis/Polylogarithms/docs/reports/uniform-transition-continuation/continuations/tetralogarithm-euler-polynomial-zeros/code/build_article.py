#!/usr/bin/env python3
"""Compile the standalone article and reject unresolved references."""
from __future__ import annotations

from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent.parent
JOB = "ProveIt_Polylogarithms_Continuation_2026-10-10"


def main() -> None:
    compiler = shutil.which("pdflatex")
    if compiler is None:
        raise SystemExit("pdflatex is required; install a TeX Live distribution.")
    for pass_number in range(1, 4):
        result = subprocess.run(
            [compiler, "-interaction=nonstopmode", "-halt-on-error",
             "-file-line-error", f"-jobname={JOB}", "article.tex"],
            cwd=ROOT, capture_output=True, text=True, check=False,
        )
        if result.returncode:
            print(result.stdout)
            print(result.stderr)
            raise SystemExit(result.returncode)
        print(f"LaTeX pass {pass_number}: complete")
    log = (ROOT / f"{JOB}.log").read_text(errors="replace")
    rejected = [
        phrase for phrase in (
            "There were undefined references",
            "multiply defined",
            "Overfull \\hbox",
            "Overfull \\vbox",
            "destination with the same identifier",
        ) if phrase in log
    ]
    if rejected:
        raise SystemExit("Review LaTeX log before delivery: " + ", ".join(rejected))
    print(ROOT / f"{JOB}.pdf")


if __name__ == "__main__":
    main()
