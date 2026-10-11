#!/usr/bin/env python3
"""Build the article and regenerate its self-contained LaTeX source."""
from __future__ import annotations

import argparse
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
STEM = "Mixed_Resolvents_Harmonic_Powers_Stieltjes_Collisions"
INPUT = re.compile(r"\\input\{([^}]+)\}")


def flatten(path: Path, stack: tuple[Path, ...] = ()) -> str:
    path = path.resolve()
    if path in stack or not path.is_relative_to(ROOT):
        raise ValueError(f"Invalid or cyclic input: {path}")
    text = path.read_text(encoding="utf-8")

    def include(match: re.Match[str]) -> str:
        name = match.group(1)
        child = ROOT / (name if name.endswith(".tex") else name + ".tex")
        relative = child.relative_to(ROOT).as_posix()
        return (f"\n% BEGIN {relative}\n"
                + flatten(child, stack + (path,))
                + f"\n% END {relative}\n")

    return INPUT.sub(include, text)


def compile_tex(source: str, cwd: Path, build_dir: Path) -> Path:
    build_dir.mkdir(parents=True, exist_ok=True)
    engine = shutil.which("pdflatex")
    if engine is None:
        raise SystemExit("pdflatex is required; install a standard TeX Live distribution.")
    env = os.environ.copy()
    env.setdefault("SOURCE_DATE_EPOCH", "1791676800")
    env.setdefault("FORCE_SOURCE_DATE", "1")
    command = [engine, "-interaction=nonstopmode", "-halt-on-error",
               "-file-line-error", f"-output-directory={build_dir}", source]
    for _ in range(3):
        result = subprocess.run(command, cwd=cwd, env=env,
                                text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT)
        if result.returncode:
            print(result.stdout)
            raise SystemExit(result.returncode)
    job = Path(source).stem
    log = (build_dir / (job + ".log")).read_text(encoding="utf-8", errors="replace")
    problems = [line for line in log.splitlines()
                if any(token in line for token in
                       ("Overfull", "Missing character", "undefined references",
                        "multiply defined", "destination with the same identifier"))]
    if problems:
        raise SystemExit("Layout/reference check failed:\n" + "\n".join(problems))
    print(next((line for line in log.splitlines() if "Output written on" in line),
               f"Compiled {source}"))
    return build_dir / (job + ".pdf")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-only", action="store_true",
                        help="Regenerate the standalone .tex without compiling.")
    parser.add_argument("--check-standalone", action="store_true",
                        help="Also compile the standalone source in an empty temporary directory.")
    args = parser.parse_args()
    standalone = ROOT / (STEM + ".tex")
    standalone.write_text(
        "% Generated from article.tex and its modular inputs by build.py.\n"
        "% This file is independently compilable; edit the modular sources first.\n"
        + flatten(ROOT / "article.tex"), encoding="utf-8")
    print(f"Wrote {standalone.name}")
    if args.source_only:
        return
    pdf = compile_tex("article.tex", ROOT, ROOT / ".build")
    shutil.copy2(pdf, ROOT / (STEM + ".pdf"))
    if args.check_standalone:
        with tempfile.TemporaryDirectory(prefix="proveit-standalone-") as name:
            temp = Path(name)
            shutil.copy2(standalone, temp / standalone.name)
            compile_tex(standalone.name, temp, temp / "build")
        print("Standalone source compiled successfully without any modular inputs.")


if __name__ == "__main__":
    main()
