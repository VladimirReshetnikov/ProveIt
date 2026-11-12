"""Rebuild the supplied PDF from its actual LaTeX sources."""
from pathlib import Path
import shutil
import subprocess

root = Path(__file__).resolve().parent
build = root / "build"
build.mkdir(exist_ok=True)
format_file = build / "pdflatex.fmt"
lookup = subprocess.run(["kpsewhich", "pdflatex.fmt"],
                        text=True, stdout=subprocess.PIPE)
extra = []
if not lookup.stdout.strip():
    if not format_file.exists():
        subprocess.run(
            ["pdftex", "-ini", "-etex", "-interaction=nonstopmode",
             "-halt-on-error", "-jobname=pdflatex", "-progname=pdflatex",
             "-output-directory=" + str(build), "pdflatex.ini"],
            cwd=root, check=True
        )
    extra = ["-fmt=" + str(format_file)]
for _ in range(2):
    result = subprocess.run(
        ["pdflatex", *extra, "-interaction=nonstopmode", "-halt-on-error",
         "-output-directory", str(build), "ipra_smaller_envelope.tex"],
        cwd=root, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT
    )
    if result.returncode:
        print(result.stdout[-14000:])
        raise SystemExit(result.returncode)
target = root / "ipra_smaller_envelope.pdf"
shutil.copyfile(build / target.name, target)
print("Built " + target.name)
