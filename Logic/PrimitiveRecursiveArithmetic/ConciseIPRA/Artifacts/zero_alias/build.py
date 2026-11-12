"""Build both PDFs offline; uses installed TeX and creates a missing format."""
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
BUILD = ROOT / ".build"

def run(command, cwd, logfile):
    with logfile.open("w") as stream:
        result = subprocess.run(command, cwd=cwd, stdout=stream,
                                stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError(f"Build failed; inspect {logfile}")

def main():
    BUILD.mkdir(exist_ok=True)
    if not shutil.which("pdflatex"):
        raise RuntimeError("pdfLaTeX is required to rebuild the PDFs")
    flags = []
    lookup = subprocess.run(["kpsewhich", "pdflatex.fmt"],
                            capture_output=True, text=True)
    if lookup.returncode or not lookup.stdout.strip():
        formats = BUILD / "texfmt"
        formats.mkdir(exist_ok=True)
        run(["pdftex", "-ini", "-etex", "-jobname=pdflatex",
             "-progname=pdflatex", "pdflatex.ini"], formats,
            BUILD / "format.log")
        flags = ["-fmt=" + str(formats / "pdflatex.fmt")]
    for document in ("ipra_zero_alias", "foundations"):
        for pass_number in range(1, 4):
            run(["pdflatex", *flags, "-interaction=nonstopmode",
                 "-halt-on-error", document + ".tex"], ROOT,
                BUILD / f"{document}-{pass_number}.log")
        print(document + ".pdf")

if __name__ == "__main__":
    main()

