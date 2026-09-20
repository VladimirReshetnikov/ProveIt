#!/usr/bin/env python3
"""Run the exact checks and rebuild article.pdf (Python 3.9+ for the CAS-free half).

The four checkers are deliberately independent:
  certificates.py              exact rational polynomial arithmetic, no CAS
  verify.py                    n<=200, ten subset and cycle triangles, GF entries
  code/verify_rows.py          n<=300, five subset triangles, block-profile entries
  code/verify_certificates.py  the same identities under SymPy (optional)
The SymPy checker is skipped with a notice if SymPy is not installed; every
identity in the article is still verified by certificates.py alone.
"""
from pathlib import Path
import importlib.util
import shutil
import subprocess
import sys


def main() -> None:
    root = Path(__file__).resolve().parent
    for command in (
        ["certificates.py"],
        ["verify.py"],
        ["code/verify_rows.py", "--max-n", "300", "--output-dir", "data"],
    ):
        subprocess.run([sys.executable] + command, cwd=root, check=True)
    if importlib.util.find_spec("sympy") is None:
        print("SymPy not installed: skipping code/verify_certificates.py "
              "(the CAS-free checks above already cover every identity).")
    else:
        subprocess.run([sys.executable, "code/verify_certificates.py",
                        "--output", "data/certificate_checks.json"],
                       cwd=root, check=True)
    latexmk = shutil.which("latexmk")
    options = ["-interaction=nonstopmode", "-halt-on-error", "article.tex"]
    if latexmk:
        subprocess.run([latexmk, "-pdf"] + options, cwd=root, check=True)
    else:
        pdflatex = shutil.which("pdflatex")
        if not pdflatex:
            raise SystemExit("Exact checks passed. PDF build needs latexmk or pdflatex on PATH.")
        for _ in range(3):
            subprocess.run([pdflatex] + options, cwd=root, check=True)
    print(f"Built {root / 'article.pdf'}")


if __name__ == "__main__":
    try:
        main()
    except subprocess.CalledProcessError as error:
        raise SystemExit(f"Build stopped: {error.cmd!r} exited with status {error.returncode}.")
