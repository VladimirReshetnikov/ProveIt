#!/usr/bin/env python3
"""Build the report with three pdflatex passes, keeping intermediates outside the packet."""
from pathlib import Path
import datetime
import os
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent


def main():
    compiler = shutil.which("pdflatex")
    if not compiler:
        raise SystemExit("pdflatex is required; see report.tex for package dependencies.")
    env = dict(os.environ)
    epoch = int(datetime.datetime(2026, 10, 21, tzinfo=datetime.timezone.utc).timestamp())
    env.setdefault("SOURCE_DATE_EPOCH", str(epoch))
    env.setdefault("FORCE_SOURCE_DATE", "1")
    with tempfile.TemporaryDirectory(prefix="k215-report-") as build:
        for pass_number in (1, 2, 3):
            command = [compiler, "-halt-on-error", "-interaction=nonstopmode",
                       "-output-directory", build, "report.tex"]
            result = subprocess.run(command, cwd=ROOT, env=env, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            if result.returncode:
                print(result.stdout)
                raise SystemExit(f"LaTeX pass {pass_number} failed.")
        log = (Path(build) / "report.log").read_text(errors="replace")
        for line in log.splitlines():
            if "Warning:" in line or "Overfull" in line:
                print(line)
        shutil.copyfile(Path(build) / "report.pdf", ROOT / "report.pdf")
    print(f"Built {ROOT / 'report.pdf'}")


if __name__ == "__main__":
    main()
