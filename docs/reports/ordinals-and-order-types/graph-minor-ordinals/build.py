#!/usr/bin/env python3
"""Compile the accompanying LaTeX manuscript with an installed pdflatex."""
from pathlib import Path
import shutil
import subprocess
import sys


def main() -> None:
    root = Path(__file__).resolve().parent
    executable = shutil.which("pdflatex")
    if executable is None:
        raise SystemExit("pdflatex was not found. Install TeX Live or MiKTeX, or use the supplied PDF.")
    command = [executable, "-interaction=nonstopmode", "-halt-on-error", "graph_minor_ordinals.tex"]
    for iteration in range(3):
        result = subprocess.run(command, cwd=root, capture_output=True, text=True, errors="replace")
        if result.returncode:
            sys.stderr.write(result.stdout[-16000:])
            sys.stderr.write(result.stderr)
            raise SystemExit(f"LaTeX pass {iteration + 1} failed; consult graph_minor_ordinals.log.")
    print(root / "graph_minor_ordinals.pdf")


if __name__ == "__main__":
    main()
