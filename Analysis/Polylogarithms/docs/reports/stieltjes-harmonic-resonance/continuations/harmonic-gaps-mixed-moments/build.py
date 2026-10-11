#!/usr/bin/env python3
"""Create the standalone TeX source and build the accompanying article."""
from pathlib import Path
import argparse
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
STEM = "Harmonic_Gaps_and_Mixed_Moments"


def expand(path):
    text = path.read_text(encoding="utf-8")

    def replace(match):
        child = path.parent / match.group(1)
        if not child.suffix:
            child = child.with_suffix(".tex")
        return ("% Begin " + str(child.relative_to(ROOT)) + "\n"
                + expand(child) + "\n% End "
                + str(child.relative_to(ROOT)) + "\n")

    return re.sub(r"\\input\{([^}]+)\}", replace, text)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-only", action="store_true")
    args = parser.parse_args()
    standalone = ROOT / (STEM + ".tex")
    standalone.write_text(
        "% Standalone source generated from article.tex and its inputs.\n"
        "% Edit the modular sources, then run python3 build.py.\n"
        + expand(ROOT / "article.tex"), encoding="utf-8")
    print("Created", standalone.name, flush=True)
    if args.source_only:
        return
    if shutil.which("latexmk") is None:
        raise SystemExit("latexmk is required; see README.md for TeX dependencies.")
    subprocess.run([
        "latexmk", "-pdf", "-interaction=nonstopmode", "-halt-on-error",
        "-file-line-error", "-outdir=build", standalone.name
    ], cwd=ROOT, check=True)
    shutil.copy2(ROOT / "build" / (STEM + ".pdf"), ROOT / (STEM + ".pdf"))
    print("Created", STEM + ".pdf", flush=True)


if __name__ == "__main__":
    main()
