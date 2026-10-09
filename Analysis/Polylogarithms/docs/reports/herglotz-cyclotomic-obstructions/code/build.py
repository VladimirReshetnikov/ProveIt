#!/usr/bin/env python3
"""Compile the article with latexmk, or with three pdfLaTeX passes.

The package root is determined from this file, preserving the article's
relative figure paths regardless of the caller's current directory.
Only the Python standard library is used. A working TeX installation and
the LaTeX packages loaded by herglotz_research.tex must already be available.

    python build.py
    python build.py --engine pdflatex
    python build.py --dry-run
"""

from __future__ import annotations

import argparse
from pathlib import Path
import shlex
import shutil
import subprocess
import sys


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--engine", choices=("auto", "latexmk", "pdflatex"), default="auto",
        help="auto prefers latexmk and falls back to three pdfLaTeX passes",
    )
    parser.add_argument(
        "--dry-run", action="store_true",
        help="display the working directory and commands without compiling",
    )
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    source = root / "herglotz_research.tex"
    if not source.is_file():
        parser.error(f"The article source is missing: {source}")

    engine = args.engine
    if engine == "auto":
        engine = "latexmk" if shutil.which("latexmk") else "pdflatex"
    executable = shutil.which(engine)
    if executable is None:
        if args.engine == "auto":
            parser.error("Neither latexmk nor pdflatex was found on PATH; install a TeX distribution.")
        parser.error(f"{engine} was not found on PATH; install it or choose another engine.")

    options = ["-interaction=nonstopmode", "-halt-on-error"]
    if engine == "latexmk":
        commands = [[executable, "-pdf", *options, source.name]]
    else:
        commands = [[executable, *options, source.name] for _ in range(3)]

    print(f"Working directory: {root}", flush=True)
    for number, command in enumerate(commands, start=1):
        print(f"[{number}/{len(commands)}] {shlex.join(command)}", flush=True)
        if args.dry_run:
            continue
        try:
            subprocess.run(command, cwd=root, check=True)
        except subprocess.CalledProcessError as error:
            print(f"Compilation failed; inspect {source.with_suffix('.log')}.", file=sys.stderr)
            return error.returncode if error.returncode > 0 else 1
        except OSError as error:
            print(f"Could not run the TeX engine: {error}", file=sys.stderr)
            return 1

    if not args.dry_run:
        print(f"Built {source.with_suffix('.pdf')}")
        if engine == "pdflatex":
            print("Check the final log for rerun warnings after pagination or reference changes.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
