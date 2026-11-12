"""Rebuild the self-contained LaTeX report with pdfLaTeX."""
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
NAME = "ipra_progress_independence"


def main():
    executable = shutil.which("pdflatex")
    if executable is None:
        raise SystemExit("pdfLaTeX is required; install a TeX Live distribution.")
    build = ROOT / "build"
    build.mkdir(exist_ok=True)
    extra = []
    lookup = subprocess.run(["kpsewhich", "pdflatex.fmt"],
                            capture_output=True, text=True)
    if not lookup.stdout.strip():
        format_file = build / "pdflatex.fmt"
        if not format_file.exists():
            initialized = subprocess.run(
                ["pdftex", "-ini", "-etex", "-interaction=nonstopmode",
                 "-halt-on-error", "-jobname=pdflatex", "-progname=pdflatex",
                 "-output-directory=" + str(build), "pdflatex.ini"],
                cwd=ROOT, capture_output=True, text=True,
            )
            (build / "format_setup.txt").write_text(
                initialized.stdout + initialized.stderr)
            if initialized.returncode:
                raise SystemExit("Local format initialization failed; inspect build/format_setup.txt")
        extra = ["-fmt=" + str(format_file)]
    for pass_number in range(1, 4):
        result = subprocess.run(
            [executable, *extra, "-no-shell-escape", "-interaction=nonstopmode", "-halt-on-error",
             "-file-line-error", "-output-directory", str(build), NAME + ".tex"],
            cwd=ROOT, capture_output=True, text=True,
        )
        (build / f"pass_{pass_number}.txt").write_text(result.stdout + result.stderr)
        if result.returncode:
            raise SystemExit(f"LaTeX failed; inspect build/pass_{pass_number}.txt")
    shutil.copyfile(build / (NAME + ".pdf"), ROOT / (NAME + ".pdf"))
    print(ROOT / (NAME + ".pdf"))


if __name__ == "__main__":
    main()
