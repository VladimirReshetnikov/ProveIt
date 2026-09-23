#!/usr/bin/env python3
"""Build article.pdf in three pdfLaTeX passes; Python 3.10+, no packages.

Intermediate files stay in .build/. Shell escape is disabled. This builder
checks typesetting, not mathematical correctness, and does not run verify.py.
"""
from __future__ import annotations
import re
import shutil
import subprocess
import sys
from pathlib import Path


def main() -> int:
    root = Path(__file__).resolve().parent
    source = root / "article.tex"
    if not source.is_file():
        print(f"Missing LaTeX source: {source}", file=sys.stderr)
        return 1
    executable = shutil.which("pdflatex")
    if executable is None:
        print("pdfLaTeX was not found. Install TeX Live or MiKTeX and add it to PATH.",
              file=sys.stderr)
        return 1
    output = root / ".build"
    output.mkdir(exist_ok=True)
    command = [executable, "-no-shell-escape", "-interaction=nonstopmode",
               "-halt-on-error", "-file-line-error", f"-output-directory={output}",
               source.name]
    try:
        for number in range(1, 4):
            result = subprocess.run(command, cwd=root, capture_output=True,
                                    text=True, encoding="utf-8", errors="replace",
                                    timeout=180, check=False)
            (output / f"pass-{number}.txt").write_text(
                result.stdout + result.stderr, encoding="utf-8")
            if result.returncode:
                print(result.stdout[-6000:], file=sys.stderr)
                print(f"pdfLaTeX failed on pass {number}; see {output}.", file=sys.stderr)
                return 1
        log = (output / "article.log").read_text(encoding="utf-8", errors="replace")
        bad = [line for line in log.splitlines() if re.search(
            r"Overfull|There were undefined references|Reference .* undefined|"
            r"Citation .* undefined|Rerun to get cross-references right", line)]
        if bad:
            print("Typesetting needs attention:\n" + "\n".join(bad), file=sys.stderr)
            return 1
        built = output / "article.pdf"
        if not built.is_file() or not built.stat().st_size:
            print("pdfLaTeX did not produce a nonempty PDF.", file=sys.stderr)
            return 1
        shutil.copy2(built, root / "article.pdf")
    except (OSError, subprocess.TimeoutExpired) as error:
        print(f"Build failed: {error}", file=sys.stderr)
        return 1
    print(f"Built {root / 'article.pdf'}")
    print("The epstopdf shell-escape warning is harmless: this article has no EPS graphics.")
    print("Run python verify.py separately for the exact finite regression checks.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
