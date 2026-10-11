#!/usr/bin/env python3
"""Regenerate the standalone TeX source and build the research article.

This script only manages the distributed article inputs and local LaTeX
outputs. Mathematical verification is a separate entry point.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parent
INPUT = re.compile(r"\\input\{([^}]+)\}")


def expand(path: Path, active: tuple[Path, ...] = ()) -> str:
    path = path.resolve()
    if not path.is_relative_to(ROOT):
        raise ValueError(f"Input outside the package: {path}")
    if path in active:
        raise ValueError(f"Cyclic TeX input: {path}")

    def replace(match: re.Match[str]) -> str:
        name = match.group(1)
        target = ROOT / (name if name.endswith(".tex") else name + ".tex")
        relative = target.relative_to(ROOT).as_posix()
        return ("\n% BEGIN EMBEDDED " + relative + "\n"
                + expand(target, active + (path,))
                + "\n% END EMBEDDED " + relative + "\n")

    return INPUT.sub(replace, path.read_text(encoding="utf-8"))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-only", action="store_true",
                        help="Regenerate article_singlefile.tex without compiling.")
    args = parser.parse_args()
    combined = ("% Self-contained source generated from article.tex and its distributed sections.\n"
                + expand(ROOT / "article.tex"))
    (ROOT / "article_singlefile.tex").write_text(combined, encoding="utf-8")
    print("Regenerated article_singlefile.tex", flush=True)
    if not args.source_only:
        subprocess.run(["latexmk", "-pdf", "-interaction=nonstopmode",
                        "-halt-on-error", "article.tex"], cwd=ROOT, check=True)


if __name__ == "__main__":
    main()
