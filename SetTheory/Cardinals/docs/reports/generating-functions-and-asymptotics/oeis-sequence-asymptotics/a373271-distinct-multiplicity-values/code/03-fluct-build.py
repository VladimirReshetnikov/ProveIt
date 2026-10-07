#!/usr/bin/env python3
"""Build both self-contained LaTeX manuscripts without installing anything.

Requires pdflatex on PATH and the standard packages named in the TeX files.
Three passes resolve tables of contents, citations, and cross-references.
Existing PDF figure components are used; no plotting dependencies are needed.
Only each manuscript's normal LaTeX output files and build-transcript.txt
are written. Source, data, and verification certificates are not changed.
"""
from pathlib import Path
import shutil
import subprocess


def main():
    root = Path(__file__).resolve().parent
    engine = shutil.which("pdflatex")
    if engine is None:
        raise SystemExit("pdflatex was not found; install a suitable TeX distribution.")
    for name in ("partitions", "sensitivity"):
        directory = root / name
        if not (directory / "article.tex").is_file():
            raise SystemExit(f"Missing source: {directory / 'article.tex'}")
        # Remove only reproducible auxiliary files, so an interrupted earlier
        # build cannot leave a partial .aux or .toc that prevents the next one.
        for suffix in (".aux", ".toc", ".out", ".fls", ".fdb_latexmk"):
            (directory / ("article" + suffix)).unlink(missing_ok=True)
        transcript = directory / "build-transcript.txt"
        with transcript.open("w", encoding="utf-8") as stream:
            for _ in range(3):
                subprocess.run(
                    [engine, "-interaction=nonstopmode", "-halt-on-error", "article.tex"],
                    cwd=directory, stdout=stream, stderr=subprocess.STDOUT, check=True,
                )
        log = (directory / "article.log").read_text(encoding="utf-8", errors="replace")
        failures = (
            "There were undefined references", "undefined on input line",
            "Overfull \\hbox", "Overfull \\vbox", "Fatal error occurred",
        )
        present = [message for message in failures if message in log]
        if present:
            raise SystemExit(f"{name}: inspect article.log for {present}")
        pdf = directory / "article.pdf"
        if not pdf.is_file() or pdf.stat().st_size == 0:
            raise SystemExit(f"No PDF produced for {name}")
        print(f"Built {name}/article.pdf ({pdf.stat().st_size:,} bytes)")


if __name__ == "__main__":
    main()
