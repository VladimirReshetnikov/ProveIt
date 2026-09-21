#!/usr/bin/env python3
"""Build article.pdf with an installed pdfLaTeX; Python 3.9+, no dependencies."""
from pathlib import Path
import shutil
import subprocess
import sys


def main() -> int:
    root = Path(__file__).resolve().parent
    compiler = shutil.which("pdflatex")
    if compiler is None:
        print("pdfLaTeX was not found. Install TeX Live or MiKTeX and ensure "
              "pdflatex is on PATH.", file=sys.stderr)
        return 1
    for run in range(1, 4):
        result = subprocess.run(
            [compiler, "-interaction=nonstopmode", "-halt-on-error", "article.tex"],
            cwd=str(root), stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            text=True, errors="replace", check=False)
        (root / ("build_pass_%d.log" % run)).write_text(result.stdout, encoding="utf-8")
        if result.returncode:
            print(result.stdout[-6000:], file=sys.stderr)
            print("Build failed; see article.log and build_pass_%d.log." % run,
                  file=sys.stderr)
            return result.returncode
    print("Built %s" % (root / "article.pdf"))
    return 0


if __name__ == "__main__":
    sys.exit(main())
