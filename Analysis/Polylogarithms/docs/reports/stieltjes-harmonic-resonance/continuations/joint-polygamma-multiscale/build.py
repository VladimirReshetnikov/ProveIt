#!/usr/bin/env python3
"""Build the standalone TeX and PDF using standard pdfLaTeX packages."""
from pathlib import Path
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
STEM = "Polygamma_Moments_and_Stieltjes_Resonances"


def expand_inputs(path: Path) -> str:
    source = path.read_text(encoding="utf-8")
    pattern = re.compile(r"\\input\{([^}]+)\}")

    def replace(match):
        child = ROOT / match.group(1)
        if not child.suffix:
            child = child.with_suffix(".tex")
        relative = child.relative_to(ROOT)
        return (f"% BEGIN {relative}\n" + expand_inputs(child)
                + f"\n% END {relative}\n")

    return pattern.sub(replace, source)


def main():
    standalone = ROOT / f"{STEM}.tex"
    standalone.write_text(expand_inputs(ROOT / "article.tex"), encoding="utf-8")
    build = ROOT / "build"
    build.mkdir(exist_ok=True)
    subprocess.run(
        ["latexmk", "-pdf", "-interaction=nonstopmode", "-halt-on-error",
         "-file-line-error", f"-outdir={build}", str(standalone)],
        cwd=ROOT, check=True,
    )
    shutil.copy2(build / f"{STEM}.pdf", ROOT / f"{STEM}.pdf")
    print(f"Built {STEM}.tex and {STEM}.pdf")


if __name__ == "__main__":
    main()
