#!/usr/bin/env python3
"""Rebuild the local research article and run its finite exact checks.

Requires Python >= 3.9 and pdfLaTeX on PATH. No third-party Python modules.
Compiler transcripts are written to build_logs/. Existing article.pdf and
verification.json are updated; delivery hashes are intentionally not rewritten.
"""
from __future__ import annotations

import shutil
import subprocess
import sys
from pathlib import Path


def main() -> int:
    root = Path(__file__).resolve().parent
    compiler = shutil.which("pdflatex")
    if compiler is None:
        print("Error: pdflatex is not on PATH. Install TeX Live or MiKTeX.", file=sys.stderr)
        return 2
    logs = root / "build_logs"
    logs.mkdir(exist_ok=True)
    try:
        subprocess.run(
            [sys.executable, str(root / "verify.py"), "--output", str(root / "verification.json")],
            cwd=root, check=True, timeout=120,
        )
        for number in range(1, 4):
            log = logs / f"pdflatex-pass-{number}.txt"
            with log.open("w", encoding="utf-8") as stream:
                subprocess.run(
                    [compiler, "-interaction=nonstopmode", "-halt-on-error", "article.tex"],
                    cwd=root, stdout=stream, stderr=subprocess.STDOUT,
                    check=True, timeout=180,
                )
        if not (root / "article.pdf").is_file():
            raise RuntimeError("The compiler returned success without creating article.pdf.")
    except (subprocess.CalledProcessError, subprocess.TimeoutExpired, OSError, RuntimeError) as exc:
        print(f"Build failed: {exc}\nCompiler transcripts: {logs}", file=sys.stderr)
        return 1
    print(f"Built: {root / 'article.pdf'}")
    print("The delivery's build_report.json and SHA256SUMS.txt have not been updated.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
