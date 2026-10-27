#!/usr/bin/env python3
"""Compile the complete report in a disposable directory, with no shell escape."""
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def main():
    engine = shutil.which("pdflatex")
    if not engine:
        raise SystemExit("pdfLaTeX is required to compile report.tex")
    with tempfile.TemporaryDirectory(prefix="sat-adaptive-four-") as work:
        work = Path(work)
        for name in ("report.tex", "k4_certificate.tex"):
            shutil.copy2(ROOT / name, work / name)
        for run in range(3):
            result = subprocess.run([engine, "-no-shell-escape", "-halt-on-error",
                                     "-interaction=nonstopmode", "report.tex"],
                                    cwd=work, capture_output=True, text=True)
            if result.returncode:
                print(result.stdout[-12000:])
                raise SystemExit(f"pdfLaTeX failed on pass {run+1}")
        log = (work / "report.log").read_text(errors="replace")
        bad = [line for line in log.splitlines()
               if "Overfull" in line or "undefined" in line.lower()
               or "Rerun to get" in line]
        if bad:
            print("\n".join(bad))
            raise SystemExit("Report needs a layout/reference correction")
        shutil.copy2(work / "report.pdf", ROOT / "report.pdf")
        results = ROOT / "results"
        results.mkdir(exist_ok=True)
        (results / "report_build.json").write_text(json.dumps({
            "status": "passed", "engine": "pdfLaTeX", "passes": 3,
            "shell_escape": False, "overfull_boxes": 0,
            "undefined_references": 0,
            "note": "Visual review is recorded separately."
        }, indent=2) + "\n")
    print(str(ROOT / "report.pdf"))


if __name__ == "__main__":
    main()
