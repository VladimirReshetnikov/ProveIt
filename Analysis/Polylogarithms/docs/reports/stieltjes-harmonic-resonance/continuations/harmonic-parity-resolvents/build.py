#!/usr/bin/env python3
"""Flatten the modular article and build the supplied PDF without network access."""
from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent
STEM = "Harmonic_Parity_and_Resolvent_Identities"
INPUT = re.compile(r"\\input\{([^}]+)\}")


def flatten(path: Path, active=()):
    path = path.resolve()
    if path in active:
        raise ValueError(f"Cyclic TeX input: {path}")
    if not path.is_relative_to(ROOT):
        raise ValueError(f"Input leaves the package: {path}")
    content = path.read_text(encoding="utf-8")

    def replace(match):
        child = ROOT / match.group(1)
        if not child.suffix:
            child = child.with_suffix(".tex")
        return ("\n% BEGIN " + str(child.relative_to(ROOT)) + "\n"
                + flatten(child, active + (path,))
                + "\n% END " + str(child.relative_to(ROOT)) + "\n")

    return INPUT.sub(replace, content)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--no-pdf", action="store_true",
                        help="Regenerate the standalone TeX only.")
    args = parser.parse_args()
    standalone = ROOT / (STEM + ".tex")
    standalone.write_text(
        "% Standalone source generated from article.tex by build.py.\n"
        "% All mathematical statements, proofs, and bibliography are included.\n"
        + flatten(ROOT / "article.tex"), encoding="utf-8")
    if args.no_pdf:
        print(standalone)
        return
    engine = shutil.which("pdflatex")
    if not engine:
        raise SystemExit("pdflatex is required. The standalone TeX is ready.")
    build_dir = ROOT / "build"
    build_dir.mkdir(exist_ok=True)
    # A fresh auxiliary state also recovers cleanly after an interrupted TeX run.
    # Only this article's generated auxiliary files are removed.
    for suffix in (".aux", ".out", ".toc"):
        (build_dir / (STEM + suffix)).unlink(missing_ok=True)
    command = [engine, "-interaction=nonstopmode", "-halt-on-error",
               "-file-line-error", "-output-directory=" + str(build_dir),
               str(standalone)]
    for pass_number in range(1, 4):
        result = subprocess.run(command, cwd=ROOT, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (build_dir / f"pass_{pass_number}.txt").write_text(result.stdout)
        if result.returncode:
            print(result.stdout[-14000:])
            raise SystemExit(result.returncode)
    log = (build_dir / (STEM + ".log")).read_text(errors="replace")
    unresolved = [line for line in log.splitlines()
                  if "undefined" in line.lower()
                  or "multiply defined" in line.lower()]
    missing = [line for line in log.splitlines() if "Missing character:" in line]
    if unresolved or missing:
        raise SystemExit("\n".join(unresolved + missing))
    shutil.copy2(build_dir / (STEM + ".pdf"), ROOT / (STEM + ".pdf"))
    overfull = [line for line in log.splitlines() if "Overfull" in line]
    record = {
        "engine": subprocess.run([engine, "--version"], text=True,
                                 stdout=subprocess.PIPE).stdout.splitlines()[0],
        "passes": 3,
        "unresolved_references": unresolved,
        "missing_glyphs": missing,
        "overfull_boxes": overfull,
        "standalone_contains_all_inputs": not bool(INPUT.search(standalone.read_text())),
        "pdf": STEM + ".pdf",
        "visual_review": "See results/document_review.json in the delivered package."
    }
    results = ROOT / "results"
    results.mkdir(exist_ok=True)
    (results / "build.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps(record, indent=2))


if __name__ == "__main__":
    main()
