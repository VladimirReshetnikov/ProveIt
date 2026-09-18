"""Zip the tracked contents of this repository at maximum compression.

Included: every file tracked by git (so untracked files and .git are left
out), except
  * this script,
  * dot files and dot directories at the repository root (.gitignore, ...),
  * PDFs that can be regenerated, i.e. a foo.pdf that sits next to a foo.tex
    (the synthesized report and the six archive reports). The talk, the arXiv
    preprint and its figure PDFs have no source of the same name and stay in.

Options:
  --all-pdf    keep every tracked *.pdf, including the regenerable ones

The archive is written to the repository root as <root-directory-name>.zip
and is itself ignored by git (*.zip).

Usage, from anywhere:  python make_archive.py [--all-pdf]
"""
from __future__ import annotations

import argparse
import os
import subprocess
import sys
import zipfile

ROOT = os.path.dirname(os.path.abspath(__file__))
SELF = os.path.basename(__file__)


def tracked_files() -> list[str]:
    out = subprocess.run(["git", "ls-files", "-z"], cwd=ROOT, check=True,
                         capture_output=True).stdout
    return [p.decode("utf-8") for p in out.split(b"\0") if p]


def regenerable_pdf(path: str, tracked: set[str]) -> bool:
    base, ext = os.path.splitext(path)
    return ext.lower() == ".pdf" and base + ".tex" in tracked


def select(files: list[str], all_pdf: bool) -> list[str]:
    tracked = set(files)
    chosen = []
    for f in files:
        if f == SELF or f.split("/", 1)[0].startswith("."):
            continue
        if not all_pdf and regenerable_pdf(f, tracked):
            continue
        if os.path.isfile(os.path.join(ROOT, f)):
            chosen.append(f)
    return sorted(chosen)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="zip the tracked repository contents")
    parser.add_argument("--all-pdf", action="store_true",
                        help="include regenerable PDFs (those with a .tex of the same name)")
    args = parser.parse_args(argv)
    name = os.path.basename(ROOT) + ".zip"
    target = os.path.join(ROOT, name)
    files = select(tracked_files(), args.all_pdf)
    with zipfile.ZipFile(target, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as zf:
        for f in files:
            zf.write(os.path.join(ROOT, f), arcname=f)
    print(f"{name}: {len(files)} files, {os.path.getsize(target):,} bytes")
    return 0


if __name__ == "__main__":
    sys.exit(main())
