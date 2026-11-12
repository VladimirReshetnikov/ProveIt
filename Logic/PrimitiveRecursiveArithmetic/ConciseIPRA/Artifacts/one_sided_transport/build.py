"""Rebuild the standalone LaTeX report using an installed TeX distribution."""
import shutil
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def main():
    if shutil.which("pdflatex") is None:
        raise SystemExit("Install a TeX distribution providing pdflatex and the packages in report.tex.")
    with tempfile.TemporaryDirectory(prefix="ipra-report-") as temporary:
        work = Path(temporary)
        shutil.copy2(ROOT / "report.tex", work / "report.tex")
        for _ in range(3):
            run = subprocess.run([
                "pdflatex", "-no-shell-escape", "-interaction=nonstopmode",
                "-halt-on-error", "report.tex"], cwd=work, capture_output=True, text=True)
            if run.returncode:
                raise SystemExit(run.stdout + run.stderr)
        log = (work / "report.log").read_text(errors="replace")
        if "undefined references" in log or "Overfull \\hbox" in log:
            raise SystemExit("Review LaTeX diagnostics before using the rebuilt PDF:\n" + log)
        shutil.copy2(work / "report.pdf", ROOT / "report.pdf")
    print("Rebuilt report.pdf. Its hash may differ from the distributed PDF metadata.")


if __name__ == "__main__":
    main()
