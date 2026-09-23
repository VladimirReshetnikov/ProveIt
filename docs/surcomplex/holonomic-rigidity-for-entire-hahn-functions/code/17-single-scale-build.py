#!/usr/bin/env python3
"""Build the self-contained manuscript with three pdfLaTeX passes.

Python 3.10+, a TeX installation, and pdflatex on PATH are required.
Auxiliary files go to .build/.  No shell escape or network access is used.
"""
from __future__ import annotations
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys


def main() -> int:
    root = Path(__file__).resolve().parent
    engine = shutil.which("pdflatex")
    if engine is None:
        raise RuntimeError("pdflatex was not found on PATH; install TeX Live or MiKTeX.")
    source = root / "article.tex"
    if not source.is_file():
        raise RuntimeError(f"Missing LaTeX source: {source}")
    build = root / ".build"
    build.mkdir(exist_ok=True)
    command = [engine, "-interaction=nonstopmode", "-halt-on-error",
               "-file-line-error", "-output-directory=.build", "article.tex"]
    for pass_number in range(1, 4):
        completed = subprocess.run(command, cwd=root, text=True,
                                   stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                   timeout=180, check=False)
        (build / f"pass-{pass_number}.txt").write_text(completed.stdout, encoding="utf-8")
        if completed.returncode != 0:
            print(completed.stdout[-8000:], file=sys.stderr)
            raise RuntimeError(f"pdfLaTeX pass {pass_number} failed; inspect .build/.")
    log = (build / "article.log").read_text(encoding="utf-8", errors="replace")
    overfull = len(re.findall(r"Overfull \\[hv]box", log))
    underfull = len(re.findall(r"Underfull \\[hv]box", log))
    warnings = re.findall(r"^(?:LaTeX|Package .*?) Warning:.*$", log, flags=re.MULTILINE)
    unresolved = bool(re.search(r"undefined references|undefined on input|Citation .* undefined", log))
    if overfull or unresolved:
        raise RuntimeError("Build has overfull boxes or unresolved references; inspect .build/article.log.")
    target = root / "article.pdf"
    shutil.copyfile(build / "article.pdf", target)
    page_count = None
    if shutil.which("pdfinfo"):
        info = subprocess.run(["pdfinfo", str(target)], text=True, capture_output=True, check=True).stdout
        match = re.search(r"^Pages:\s*(\d+)", info, flags=re.MULTILINE)
        if match:
            page_count = int(match.group(1))
    report = {"status": "passed", "passes": 3, "pages": page_count,
              "overfull_boxes": overfull, "underfull_boxes": underfull,
              "latex_warnings": warnings, "undefined_references": unresolved,
              "pdf_bytes": target.stat().st_size,
              "scope": "Compilation and log checks; not mathematical proof verification."}
    (root / "build_audit.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, RuntimeError, subprocess.SubprocessError) as exc:
        print(f"Build failed: {exc}", file=sys.stderr)
        raise SystemExit(1)
