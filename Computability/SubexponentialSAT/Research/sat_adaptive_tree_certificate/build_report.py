#!/usr/bin/env python3
"""Compile the complete LaTeX report with shell escape disabled."""
from pathlib import Path
import json
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent


def main():
    if not shutil.which("pdflatex"):
        raise RuntimeError("pdfLaTeX is required to rebuild the report")
    build = ROOT / "_build"
    build.mkdir(exist_ok=True)
    command = ["pdflatex", "-interaction=nonstopmode", "-halt-on-error",
               "-no-shell-escape", "-output-directory="+str(build), "report.tex"]
    for _ in range(3):
        result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
        if result.returncode:
            raise RuntimeError(result.stdout[-6000:]+result.stderr)
    log = (build/"report.log").read_text(encoding="utf-8", errors="replace")
    errors = [line for line in log.splitlines()
              if "Overfull" in line or "undefined references" in line
              or re.search(r"(?:Reference|Citation).*undefined", line)]
    if errors:
        raise RuntimeError("Report QA failed:\n"+"\n".join(errors))
    shutil.copyfile(build/"report.pdf", ROOT/"report.pdf")
    (ROOT/"results").mkdir(exist_ok=True)
    (ROOT/"results"/"latex_build.log").write_text(log, encoding="utf-8")
    result = {"status": "PASS", "passes": 3, "shell_escape": False,
              "overfull_boxes": 0, "undefined_references": 0,
              "pdf_bytes": (ROOT/"report.pdf").stat().st_size}
    (ROOT/"results"/"build_validation.json").write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
