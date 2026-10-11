#!/usr/bin/env python3
"""Build the editable modular article and its self-contained TeX/PDF deliverables."""
from pathlib import Path
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]
STEM = "Harmonic_Tails_Shifts_and_Twists"
INPUT = re.compile(r"\\input\{([^}]+)\}")


def flatten(path: Path, active=()):
    path = path.resolve()
    if path in active:
        raise ValueError(f"Circular TeX input: {path}")
    if not path.is_relative_to(ROOT):
        raise ValueError(f"Input escapes article directory: {path}")
    source = path.read_text(encoding="utf-8")
    def include(match):
        target = path.parent / match.group(1)
        if not target.suffix:
            target = target.with_suffix(".tex")
        return (f"% BEGIN INCLUDED SOURCE: {target.relative_to(ROOT)}\n"
                + flatten(target, active + (path,))
                + f"\n% END INCLUDED SOURCE: {target.relative_to(ROOT)}\n")
    return INPUT.sub(include, source)


def main():
    standalone = ROOT / f"{STEM}.tex"
    standalone.write_text(
        "% Standalone source; regenerate with python3 tools/build_article.py.\n"
        + flatten(ROOT / "article.tex"), encoding="utf-8")
    build = ROOT / "build"
    build.mkdir(exist_ok=True)
    subprocess.run([
        "latexmk", "-pdf", "-interaction=nonstopmode", "-halt-on-error",
        "-file-line-error", "-outdir=build", standalone.name
    ], cwd=ROOT, check=True)
    shutil.copyfile(build / f"{STEM}.pdf", ROOT / f"{STEM}.pdf")
    print(f"Built {standalone.name} and {STEM}.pdf")


if __name__ == "__main__":
    main()
