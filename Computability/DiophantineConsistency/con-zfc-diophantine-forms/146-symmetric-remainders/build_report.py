#!/usr/bin/env python3
"""Rebuild the typeset report using pdfLaTeX, with temporary build products."""
import argparse
import re
import shutil
import subprocess
import tempfile
from pathlib import Path
import verify

ROOT = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "report.pdf")
    args = parser.parse_args()
    verify.check_text()
    if not shutil.which("pdflatex"):
        raise SystemExit("pdfLaTeX is required; install a standard TeX Live or MiKTeX distribution.")
    with tempfile.TemporaryDirectory(prefix="conzfc-report-") as tmp:
        command = ["pdflatex", "-interaction=nonstopmode", "-halt-on-error",
                   "-output-directory=" + tmp, "report.tex"]
        for _ in range(3):
            run = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
            if run.returncode:
                raise SystemExit(run.stdout[-12000:] + run.stderr[-3000:])
        log = (Path(tmp) / "report.log").read_text()
        failures = re.findall(r"Overfull \\[hv]box[^\n]*|LaTeX Warning: (?:There were undefined|Reference[^\n]*undefined|Citation[^\n]*undefined)[^\n]*", log)
        if failures:
            raise SystemExit("Report layout/reference checks failed:\n" + "\n".join(failures))
        args.output.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(Path(tmp) / "report.pdf", args.output)
    print(args.output.resolve())


if __name__ == "__main__":
    main()
