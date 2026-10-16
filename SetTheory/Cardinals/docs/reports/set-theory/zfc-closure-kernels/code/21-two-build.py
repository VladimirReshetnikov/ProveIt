#!/usr/bin/env python3
"""Build report.pdf from report.tex with an installed LaTeX distribution."""
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def main():
    engine = shutil.which("pdflatex")
    if engine is None:
        raise SystemExit("pdflatex is required; install TeX Live or MiKTeX.")
    build = ROOT / ".build"
    build.mkdir(exist_ok=True)
    command = [
        engine, "-interaction=nonstopmode", "-halt-on-error",
        "-file-line-error", "-output-directory", str(build), "report.tex",
    ]
    for number in range(1, 4):
        result = subprocess.run(command, cwd=ROOT, text=True,
                                stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT)
        (build / f"pass-{number}.txt").write_text(result.stdout)
        if result.returncode:
            print("\n".join(result.stdout.splitlines()[-70:]), file=sys.stderr)
            raise SystemExit(result.returncode)
        print(f"LaTeX pass {number}/3 completed.")
    log = (build / "report.log").read_text(errors="replace")
    if "There were undefined references" in log:
        raise SystemExit("Unresolved references: inspect .build/report.log.")
    shutil.copyfile(build / "report.pdf", ROOT / "report.pdf")
    print(f"Built {ROOT / 'report.pdf'}")


if __name__ == "__main__":
    main()
