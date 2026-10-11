#!/usr/bin/env python3
"""Flatten the modular article and build its self-contained PDF.

Usage: python build.py [--tex-only]
No network access is used. A TeX installation with the packages listed in
article.tex is required for PDF compilation.
"""
from __future__ import annotations

import argparse
import re
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent
STEM = "Bernoulli_Tornheim_Digamma_Identities"


def expand(path: Path, ancestors=()) -> str:
    path = path.resolve()
    if path in ancestors:
        raise ValueError(f"Cyclic TeX input: {path}")
    source = path.read_text(encoding="utf-8")
    pattern = re.compile(r"\\input\{([^}]+)\}")

    def replace(match):
        child = ROOT / match.group(1)
        if not child.suffix:
            child = child.with_suffix(".tex")
        return (f"\n% BEGIN {child.relative_to(ROOT)}\n"
                + expand(child, ancestors + (path,))
                + f"\n% END {child.relative_to(ROOT)}\n")

    return pattern.sub(replace, source)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--tex-only", action="store_true")
    args = parser.parse_args()
    target = ROOT / f"{STEM}.tex"
    target.write_text(expand(ROOT / "article.tex"), encoding="utf-8")
    print(f"Wrote {target.name}", flush=True)
    if args.tex_only:
        return
    engine = shutil.which("pdflatex")
    if engine is None:
        raise SystemExit("pdflatex was not found; the flattened TeX is ready.")
    scratch = ROOT / "build"
    scratch.mkdir(exist_ok=True)
    for iteration in range(3):
        proc = subprocess.run(
            [engine, "-interaction=nonstopmode", "-halt-on-error",
             f"-output-directory={scratch}", target.name],
            cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        )
        (scratch / f"pass-{iteration + 1}.txt").write_text(proc.stdout)
        if proc.returncode:
            print(proc.stdout[-10000:])
            raise SystemExit(proc.returncode)
    log = (scratch / f"{STEM}.log").read_text(errors="replace")
    bad = [line for line in log.splitlines()
           if ("undefined" in line.lower() or "multiply defined" in line.lower()
               or "Overfull" in line)]
    shutil.copyfile(scratch / f"{STEM}.pdf", ROOT / f"{STEM}.pdf")
    print(f"Wrote {STEM}.pdf", flush=True)
    if bad:
        print("Layout or reference notices:")
        print("\n".join(bad))
    else:
        print("No overfull boxes or unresolved-reference notices.")


if __name__ == "__main__":
    main()
