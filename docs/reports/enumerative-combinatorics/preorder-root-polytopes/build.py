#!/usr/bin/env python3
"""Compile article.tex twice with pdfLaTeX; works on Windows, macOS, and Linux."""
from __future__ import annotations

import shutil
import subprocess
from pathlib import Path


def main() -> None:
    root = Path(__file__).resolve().parent
    engine = shutil.which("pdflatex")
    if engine is None:
        raise SystemExit("pdfLaTeX was not found. Install TeX Live or MiKTeX and put pdflatex on PATH.")
    build = root / "build"
    build.mkdir(exist_ok=True)
    command = [engine, "-interaction=nonstopmode", "-halt-on-error",
               f"-output-directory={build}", "article.tex"]
    with (build / "compile_stdout.txt").open("w", encoding="utf-8") as log:
        for pass_number in (1, 2):
            print(f"pdfLaTeX pass {pass_number}/2", flush=True)
            completed = subprocess.run(command, cwd=root, stdout=log, stderr=subprocess.STDOUT,
                                       check=False)
            if completed.returncode:
                raise SystemExit(f"pdfLaTeX failed. See {build / 'compile_stdout.txt'}")
    target = root / "article.pdf"
    shutil.copy2(build / "article.pdf", target)
    print(f"Created {target}")


if __name__ == "__main__":
    main()
