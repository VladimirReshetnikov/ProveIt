#!/usr/bin/env python3
"""Rebuild report.pdf without modifying delivered source or result files."""
from argparse import ArgumentParser
from pathlib import Path
import re
import shutil
import subprocess


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", default="replay_build",
                        help="build directory, relative to the archive root by default")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    target = Path(args.output_dir)
    if not target.is_absolute():
        target = root / target
    target.mkdir(parents=True, exist_ok=True)
    engine = shutil.which("pdflatex")
    if engine is None:
        raise SystemExit("pdflatex is required; no software is downloaded by this script.")
    command = [
        engine, "-no-shell-escape", "-interaction=nonstopmode",
        "-halt-on-error", "-file-line-error",
        "-output-directory=" + str(target), "report.tex",
    ]
    for turn in range(3):
        result = subprocess.run(command, cwd=root, capture_output=True, text=True,
                                errors="replace")
        (target / ("pass_" + str(turn + 1) + ".log")).write_text(result.stdout + result.stderr)
        if result.returncode:
            raise SystemExit("TeX compilation failed; inspect " + str(target))
    log = (target / "report.log").read_text(errors="replace")
    patterns = [
        r"Overfull \\[hv]box",
        r"LaTeX Warning: There were undefined references",
        r"LaTeX Warning: (?:Reference|Citation) .* undefined",
        r"LaTeX Warning: Label\(s\) may have changed",
        r"^! ",
    ]
    issues = [pattern for pattern in patterns if re.search(pattern, log, re.MULTILINE)]
    if issues:
        raise SystemExit("PDF built, but a layout/reference gate failed: " +
                         "; ".join(issues) + ". Inspect " + str(target / "report.log"))
    print("PASS: compilation, references, and overflow checks.")
    print(target / "report.pdf")


if __name__ == "__main__":
    main()
