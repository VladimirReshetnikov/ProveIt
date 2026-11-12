"""Assemble a standalone report and compile it twice with pdfLaTeX."""
import ast
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parent


def main():
    text = "\n".join((ROOT / name).read_text()
                     for name in ["front.tex", "proof.tex", "closing.tex"])
    substitutions = {
        "%%METRICS_TABLE%%": (ROOT / "evidence/metrics_table.tex").read_text(),
        "%%VALIDATION_SUMMARY%%": (ROOT / "evidence/validation_summary.tex").read_text(),
        "%%CHECKER_SOURCE%%": ast.unparse(ast.parse((ROOT / "code/checker.py").read_text())),
    }
    for marker, content in substitutions.items():
        if text.count(marker) != 1:
            raise RuntimeError("Missing or repeated marker: " + marker)
        text = text.replace(marker, content)
    (ROOT / "report.tex").write_text(text)
    for _ in range(2):
        run = subprocess.run(
            ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "report.tex"],
            cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (ROOT / "evidence/latex_build.log").write_text(run.stdout)
        if run.returncode:
            print(run.stdout[-6000:])
            raise SystemExit(run.returncode)
    print("Built report.tex and report.pdf")


if __name__ == "__main__":
    main()
