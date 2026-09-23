#!/usr/bin/env python3
"""Build article.tex with three pdflatex passes. Uses no network or shell escape."""
from pathlib import Path
import shutil
import subprocess
import sys


def main() -> None:
    root = Path(__file__).resolve().parent
    compiler = shutil.which("pdflatex")
    if compiler is None:
        raise SystemExit("pdflatex was not found. Install TeX Live or MiKTeX and add it to PATH.")
    for index in range(1, 4):
        command = [compiler, "-interaction=nonstopmode", "-halt-on-error", "article.tex"]
        try:
            result = subprocess.run(command, cwd=root, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT, text=True, errors="replace", timeout=180)
        except (OSError, subprocess.TimeoutExpired) as exc:
            raise SystemExit(f"Build pass {index} failed: {exc}") from exc
        (root / f"rebuild-pass-{index}.log").write_text(result.stdout, encoding="utf-8")
        if result.returncode:
            print(result.stdout[-5000:], file=sys.stderr)
            raise SystemExit(f"pdflatex pass {index} returned {result.returncode}; inspect its log.")
    print(f"Built {root / 'article.pdf'}")


if __name__ == "__main__":
    main()
