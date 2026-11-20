#!/usr/bin/env python3
"""Compile the self-contained LaTeX report with an installed pdfLaTeX."""
from pathlib import Path
import json
import os
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent


def main():
    engine = os.environ.get("IPRA_PDFLATEX") or shutil.which("pdflatex")
    if not engine:
        raise SystemExit("pdfLaTeX is required; install TeX Live or set IPRA_PDFLATEX.")
    with tempfile.TemporaryDirectory(prefix="ipra-tex-") as temporary:
        out = Path(temporary)
        logs = []
        for attempt in range(3):
            run = subprocess.run([engine, "-no-shell-escape", "-interaction=nonstopmode",
                                  "-halt-on-error", "-file-line-error",
                                  f"-output-directory={out}", "report.tex"],
                                 cwd=ROOT / "paper", text=True, capture_output=True)
            logs.append(run.stdout + run.stderr)
            if run.returncode:
                (ROOT / "evidence/pdf_build.log").write_text("\n".join(logs))
                raise SystemExit(f"LaTeX pass {attempt + 1} failed; see evidence/pdf_build.log.")
        final_log = (out / "report.log").read_text(errors="replace")
        problems = [line for line in final_log.splitlines()
                    if "Overfull" in line or "undefined" in line
                    or "Missing character" in line or "multiply defined" in line]
        (ROOT / "evidence/pdf_build.log").write_text(final_log)
        shutil.copy2(out / "report.pdf", ROOT / "paper/report.pdf")
        receipt = {"engine": engine, "passes": 3, "exit_code": 0,
                   "layout_warnings": problems,
                   "visual_review": "separate required review; not performed by this script"}
        (ROOT / "evidence/pdf_build.json").write_text(json.dumps(receipt, indent=2) + "\n")
        if problems:
            raise SystemExit("PDF compiled but needs layout/reference fixes:\n" + "\n".join(problems))
    print("PDF compiled; final log has no overfull, missing-character, or undefined-reference warnings.")


if __name__ == "__main__":
    main()
