#!/usr/bin/env python3
"""Compile all standalone papers and the collected report without network access."""
from pathlib import Path
import argparse
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
PAPERS = [
    Path("papers/gram_determinants/gram_determinants.tex"),
    Path("papers/positive_filters/positive_filters.tex"),
    Path("papers/bilinear_detection/bilinear_detection.tex"),
]

def compile_tex(relative):
    source = ROOT / relative
    log = source.with_suffix(".build.txt")
    for pass_number in range(1, 4):
        completed = subprocess.run(
            ["pdflatex", "-interaction=nonstopmode", "-halt-on-error",
             "-file-line-error", source.name],
            cwd=source.parent, capture_output=True, text=True,
        )
        with log.open("w" if pass_number == 1 else "a") as out:
            out.write(f"\n=== pass {pass_number} ===\n")
            out.write(completed.stdout)
            out.write(completed.stderr)
        if completed.returncode:
            raise RuntimeError(f"LaTeX failed: {relative}; see {log.relative_to(ROOT)}")
    last_log = source.with_suffix(".log").read_text(errors="replace")
    issues = [line for line in last_log.splitlines()
              if "Overfull" in line or "undefined" in line.lower()]
    if issues:
        print(f"Review {relative}:")
        print("\n".join(issues))
    print(f"Built {relative.with_suffix('.pdf')}", flush=True)

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--figures", action="store_true",
                        help="regenerate the detection-profile figure first")
    args = parser.parse_args()
    if args.figures:
        subprocess.run([sys.executable, "plot_profiles.py"],
                       cwd=ROOT / "papers/bilinear_detection", check=True)
    for paper in PAPERS:
        compile_tex(paper)
    compile_tex(Path("research_report.tex"))

if __name__ == "__main__":
    main()
