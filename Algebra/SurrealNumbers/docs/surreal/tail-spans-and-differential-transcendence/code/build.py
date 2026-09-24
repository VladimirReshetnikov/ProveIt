#!/usr/bin/env python3
"""Build article.pdf with three pdfLaTeX passes; no BibTeX or shell escape."""
from __future__ import annotations
import shutil
import subprocess
from pathlib import Path


def main() -> None:
    root = Path(__file__).resolve().parent
    compiler = shutil.which("pdflatex")
    if compiler is None:
        raise SystemExit("pdfLaTeX was not found. Install TeX Live or MiKTeX and the packages named in article.tex.")
    logs = root / "build_logs"
    logs.mkdir(exist_ok=True)
    for pass_number in range(1, 4):
        run = subprocess.run(
            [compiler, "-interaction=nonstopmode", "-halt-on-error", "article.tex"],
            cwd=root, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            encoding="utf-8", errors="replace", check=False,
        )
        log_path = logs / f"pass-{pass_number}.txt"
        log_path.write_text(run.stdout, encoding="utf-8")
        if run.returncode:
            print("\n".join(run.stdout.splitlines()[-40:]))
            raise SystemExit(f"pdfLaTeX failed on pass {pass_number}; see {log_path}")
        print(f"Pass {pass_number}: complete")
    print(f"Built: {root / 'article.pdf'}")


if __name__ == "__main__":
    main()
