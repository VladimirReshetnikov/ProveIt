#!/usr/bin/env python3
"""Build report.pdf with an ordinary TeX installation, without network access."""
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent


def main():
    compiler = shutil.which("pdflatex")
    if compiler is None:
        raise SystemExit("pdflatex is required to rebuild the supplied report.pdf")
    with tempfile.TemporaryDirectory(prefix="diophantine-report-") as folder:
        output = Path(folder)
        command = [compiler, "-interaction=nonstopmode", "-halt-on-error",
                   "-file-line-error", "-output-directory", str(output),
                   "report.tex"]
        for run in (1, 2):
            result = subprocess.run(command, cwd=ROOT, text=True,
                                    stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT)
            if result.returncode:
                print(result.stdout)
                raise SystemExit("TeX compilation failed on pass " + str(run))
        pdf = output / "report.pdf"
        if not pdf.is_file() or not pdf.read_bytes().startswith(b"%PDF-"):
            raise SystemExit("The TeX compiler did not produce a PDF")
        shutil.copyfile(pdf, ROOT / "report.pdf")
        warnings = [line for line in (output / "report.log").read_text(
            errors="replace").splitlines()
                    if any(word in line for word in
                           ("Overfull", "Underfull", "Warning"))]
        print("Created " + str(ROOT / "report.pdf"))
        if warnings:
            print("TeX diagnostics:\n" + "\n".join(warnings))
    print("Rebuilding the PDF can change its metadata; exact mathematical "
          "verification is a separate operation.")


if __name__ == "__main__":
    main()
