#!/usr/bin/env python3
"""Compile the report and reject unresolved references or overflowing boxes."""
from pathlib import Path
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent


def main():
    executable = shutil.which("pdflatex")
    if not executable:
        raise SystemExit("Install pdfLaTeX and the packages in report.tex.")
    for iteration in range(3):
        result = subprocess.run(
            [executable, "-no-shell-escape", "-interaction=nonstopmode",
             "-halt-on-error", "report.tex"], cwd=ROOT,
            capture_output=True, text=True)
        if result.returncode:
            print(result.stdout[-12000:])
            raise SystemExit(result.returncode)
    log = (ROOT / "report.log").read_text(errors="replace")
    forbidden = [r"There were undefined references", r"Citation .* undefined",
                 r"Reference .* undefined", r"Overfull \\[hv]box",
                 r"Undefined control sequence", r"Label .* multiply defined"]
    if any(re.search(pattern, log) for pattern in forbidden):
        print("\n".join(line for line in log.splitlines()
                        if "undefined" in line or "Overfull" in line
                        or "multiply defined" in line))
        raise SystemExit("Resolve layout or reference errors in report.log.")
    print("Built report.pdf with resolved references and no overfull boxes.")


if __name__ == "__main__":
    main()
