#!/usr/bin/env python3
"""Build the paper; create a temporary TeX format if the installation lacks it."""
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent

def run(command, cwd):
    p = subprocess.run(command, cwd=cwd, text=True,
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if p.returncode:
        raise RuntimeError(p.stdout[-14000:])
    return p.stdout

def main():
    latex, pdftex, kpse = (shutil.which(x) for x in ("pdflatex", "pdftex", "kpsewhich"))
    if not all((latex, pdftex, kpse)):
        raise SystemExit("Install TeX Live with pdflatex.")
    found = subprocess.run([kpse, "pdflatex.fmt"], cwd=ROOT,
                           text=True, capture_output=True).stdout.strip()
    with tempfile.TemporaryDirectory(prefix="ipra_tex_") as tmp:
        flags = []
        if not found:
            run([pdftex, "-ini", "-interaction=nonstopmode", "-halt-on-error",
                 "-jobname=pdflatex", "-progname=pdflatex", "-etex", "pdflatex.ini"], tmp)
            flags = ["-fmt=" + str(Path(tmp) / "pdflatex.fmt")]
        for _ in range(3):
            log = run([latex, *flags, "-interaction=nonstopmode", "-halt-on-error",
                       "ipra_crossed_uniqueness.tex"], ROOT)
    (ROOT / "evidence/latex_build.txt").write_text(log)
    print(ROOT / "ipra_crossed_uniqueness.pdf")

if __name__ == "__main__":
    main()

