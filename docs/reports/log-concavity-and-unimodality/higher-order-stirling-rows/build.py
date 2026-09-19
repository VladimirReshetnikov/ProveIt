#!/usr/bin/env python3
"""Run the exact checks and rebuild article.pdf (Python 3.9+)."""
from pathlib import Path
import shutil
import subprocess
import sys


def main() -> None:
    root = Path(__file__).resolve().parent
    for script in ("certificates.py", "verify.py"):
        subprocess.run([sys.executable, script], cwd=root, check=True)
    latexmk = shutil.which("latexmk")
    options = ["-interaction=nonstopmode", "-halt-on-error", "article.tex"]
    if latexmk:
        subprocess.run([latexmk, "-pdf"] + options, cwd=root, check=True)
    else:
        pdflatex = shutil.which("pdflatex")
        if not pdflatex:
            raise SystemExit("Exact checks passed. PDF build needs latexmk or pdflatex on PATH.")
        for _ in range(2):
            subprocess.run([pdflatex] + options, cwd=root, check=True)
    print(f"Built {root / 'article.pdf'}")


if __name__ == "__main__":
    try:
        main()
    except subprocess.CalledProcessError as error:
        raise SystemExit(f"Build stopped: {error.cmd!r} exited with status {error.returncode}.")
