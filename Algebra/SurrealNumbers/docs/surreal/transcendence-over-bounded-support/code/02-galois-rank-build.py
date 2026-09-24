#!/usr/bin/env python3
"""Build the companion LaTeX article and optionally run its finite tests.

Requires Python >= 3.10 and an installed pdfLaTeX distribution with the packages
listed in the .tex preamble. Run from any directory. No network calls are made.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import re
import shutil
import subprocess
import sys


def run_checked(command: list[str], cwd: Path, transcript: Path) -> None:
    """Run a local command, retaining its complete console output."""
    with transcript.open("w", encoding="utf-8") as output:
        result = subprocess.run(command, cwd=cwd, stdout=output,
                                stderr=subprocess.STDOUT, check=False)
    if result.returncode:
        tail = transcript.read_text(encoding="utf-8", errors="replace")[-5000:]
        raise RuntimeError(f"Command failed (status {result.returncode}).\n"
                           f"Transcript: {transcript}\n{tail}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify", action="store_true",
                        help="Also rerun the exact finite regression checks")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    source = root / "galois_rank_dichotomy.tex"
    if not source.is_file():
        raise SystemExit(f"Missing article source: {source}")
    executable = shutil.which("pdflatex")
    if executable is None:
        raise SystemExit("pdfLaTeX was not found. Install TeX Live or MiKTeX "
                         "with the packages named in the source preamble.")
    data = root / "data"
    data.mkdir(exist_ok=True)
    command = [executable, "-interaction=nonstopmode", "-halt-on-error",
               "-file-line-error", source.name]
    try:
        for pass_number in range(1, 4):
            run_checked(command, root, data / f"build_pass_{pass_number}.txt")
        log = source.with_suffix(".log").read_text(encoding="utf-8", errors="replace")
        fatal = re.findall(
            r"^.*(?:Overfull|undefined references|undefined citations|"
            r"Reference .* undefined|Citation .* undefined|"
            r"Label\(s\) may have changed|Rerun to get).*$", log, re.MULTILINE)
        if fatal:
            raise RuntimeError("Final-pass diagnostics need attention:\n" + "\n".join(fatal))
        warnings = re.findall(r"^.*(?:Warning|Underfull).*$", log, re.MULTILINE)
        if warnings:
            print("Remaining diagnostics:\n" + "\n".join(warnings))
        else:
            print("No final-pass LaTeX warnings or overfull/underfull boxes.")
        pdf = source.with_suffix(".pdf")
        if not pdf.is_file() or pdf.stat().st_size == 0:
            raise RuntimeError("The build did not produce a nonempty PDF.")
        print(f"PDF built: {pdf}")
        if args.verify:
            run_checked([sys.executable, str(root / "code" / "verify.py")],
                        root, data / "verification_console.txt")
            print((data / "verification_console.txt").read_text(encoding="utf-8"))
    except (OSError, RuntimeError) as exc:
        raise SystemExit(str(exc)) from exc


if __name__ == "__main__":
    main()
