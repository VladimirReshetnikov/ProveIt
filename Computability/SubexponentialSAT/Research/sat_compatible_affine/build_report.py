#!/usr/bin/env python3
"""Build the complete local LaTeX report; no network access is needed."""
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


def main():
    root = Path(__file__).resolve().parent
    engine = shutil.which("pdflatex")
    if engine is None:
        raise SystemExit("pdflatex is required (TeX Live with the packages in report.tex).")
    with tempfile.TemporaryDirectory(prefix="sat-report-build-") as temporary:
        build = Path(temporary)
        command = [engine, "-interaction=nonstopmode", "-halt-on-error",
                   "-file-line-error", f"-output-directory={build}", "report.tex"]
        logs = []
        # Three passes resolve the table of contents and all cross references.
        for pass_number in range(1, 4):
            run = subprocess.run(command, cwd=root, text=True,
                                 stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            logs.append(f"LaTeX pass {pass_number}\n{run.stdout}")
            if run.returncode:
                print(run.stdout, file=sys.stderr)
                raise SystemExit(run.returncode)
        final_log = (build / "report.log").read_text(errors="replace")
        result_dir = root / "results"
        result_dir.mkdir(exist_ok=True)
        (result_dir / "report_build.log").write_text("\n".join(logs))
        problems = [line for line in final_log.splitlines()
                    if "Overfull" in line or "undefined" in line
                    or "Rerun to get" in line]
        if problems:
            raise RuntimeError("Resolve LaTeX layout/reference warnings:\n" + "\n".join(problems))
        shutil.copy2(build / "report.pdf", root / "report.pdf")
        print(f"Built {root / 'report.pdf'}")


if __name__ == "__main__":
    main()
