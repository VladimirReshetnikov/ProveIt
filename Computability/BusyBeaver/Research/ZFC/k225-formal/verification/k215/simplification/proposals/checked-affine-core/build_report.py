#!/usr/bin/env python3
"""Rebuild the report without modifying the archived PDF or its receipts."""
from pathlib import Path
import argparse
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=root / "build" / "report.pdf")
    args = parser.parse_args()
    out = args.output.resolve()
    out.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="k215-report-") as tmp:
        build = Path(tmp)
        for source in root.glob("*.tex"):
            shutil.copy2(source, build / source.name)
        command = ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "report.tex"]
        for attempt in range(1, 4):
            result = subprocess.run(command, cwd=build, text=True, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT)
            if result.returncode:
                print(result.stdout)
                raise SystemExit(f"LaTeX pass {attempt} failed ({result.returncode}).")
        shutil.copy2(build / "report.pdf", out)
        shutil.copy2(build / "report.log", out.with_suffix(".log"))
    print(out)


if __name__ == "__main__":
    main()
