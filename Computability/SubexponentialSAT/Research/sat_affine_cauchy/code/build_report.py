#!/usr/bin/env python3
"""Build the report, with no shell escape, and reject unresolved references."""
from pathlib import Path
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]

def main():
    executable = shutil.which("pdflatex")
    if not executable:
        raise SystemExit("Install pdfLaTeX and the packages listed in report.tex.")
    if not (ROOT / "figures/affine_classes.png").exists():
        raise SystemExit("The included figure is missing; run code/make_figures.py first.")
    for iteration in range(3):
        run = subprocess.run([executable, "-no-shell-escape", "-interaction=nonstopmode",
                              "-halt-on-error", "report.tex"], cwd=ROOT,
                             text=True, capture_output=True)
        if run.returncode:
            print(run.stdout[-14000:])
            raise SystemExit(run.returncode)
    log = (ROOT / "report.log").read_text(errors="replace")
    fatal = [r"There were undefined references", r"Citation .* undefined",
             r"Reference .* undefined", r"Overfull \\[hv]box"]
    if any(re.search(pattern, log) for pattern in fatal):
        print("\n".join(line for line in log.splitlines()
                        if "undefined" in line or "Overfull" in line))
        raise SystemExit("Resolve the reported layout/reference issues in report.log.")
    print(f"Built {ROOT / 'report.pdf'}")

if __name__ == "__main__":
    main()
