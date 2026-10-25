#!/usr/bin/env python3
"""Build the report PDF and single-file TeX edition; keep auxiliaries temporary."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
REPORT = ROOT / "report"


def standalone_text():
    def expand(path, stack):
        resolved = path.resolve()
        if resolved in stack:
            raise ValueError("Recursive TeX input")
        text = path.read_text()
        def include(match):
            name = match.group(1)
            child = REPORT / name
            if child.parent.resolve() != REPORT.resolve() or child.suffix != ".tex":
                raise ValueError("Unexpected TeX input: " + name)
            return "% BEGIN " + name + "\n" + expand(child, stack + [resolved]) + "% END " + name + "\n"
        return re.sub(r"\\input\{([^}]+)\}", include, text)
    return expand(REPORT / "report.tex", [])


def main():
    executable = shutil.which("pdflatex")
    if executable is None:
        raise SystemExit("pdflatex is required to build this document")
    (REPORT / "report_standalone.tex").write_text(standalone_text())
    env = dict(os.environ)
    env["SOURCE_DATE_EPOCH"] = "1792963799"
    env["FORCE_SOURCE_DATE"] = "1"
    with tempfile.TemporaryDirectory(prefix="conzfc-report-") as td:
        target = Path(td)
        for p in REPORT.glob("*.tex"):
            shutil.copy2(p, target / p.name)
        command = [executable, "-interaction=nonstopmode", "-halt-on-error", "-file-line-error", "report.tex"]
        previous_aux = None
        log = ""
        for iteration in range(5):
            run = subprocess.run(command, cwd=target, env=env, capture_output=True, text=True)
            log = (target / "report.log").read_text(errors="replace") if (target / "report.log").exists() else run.stdout
            if run.returncode:
                raise SystemExit("pdfLaTeX failed:\n" + run.stdout[-12000:])
            current_aux = (target / "report.aux").read_bytes()
            if iteration >= 2 and current_aux == previous_aux and "Rerun to get" not in log and "Table widths have changed" not in log:
                break
            previous_aux = current_aux
        else:
            raise SystemExit("TeX references did not converge after five passes")
        bad = [line for line in log.splitlines() if "Overfull" in line or "undefined" in line.lower() or "LaTeX Warning:" in line]
        if bad:
            # The PDF is kept for visual review, but a release should fix these.
            shutil.copy2(target / "report.pdf", REPORT / "report.pdf")
            print("Layout/reference diagnostics:\n" + "\n".join(bad))
            raise SystemExit(2)
        shutil.copy2(target / "report.pdf", REPORT / "report.pdf")
        print("Built report/report.pdf and report/report_standalone.tex with converged references and no overfull boxes.")


if __name__ == "__main__":
    main()
