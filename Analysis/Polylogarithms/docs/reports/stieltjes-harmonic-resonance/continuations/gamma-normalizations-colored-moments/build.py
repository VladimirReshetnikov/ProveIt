#!/usr/bin/env python3
"""Build the self-contained TeX and PDF from the modular article sources."""
from __future__ import annotations

import argparse
from pathlib import Path
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
STEM = "Gamma_Determinants_and_Colored_Stieltjes_Moments"


def expand(path: Path, ancestors: tuple[Path, ...] = ()) -> str:
    path = path.resolve()
    if path in ancestors:
        raise RuntimeError(f"Recursive input: {path}")
    text = path.read_text(encoding="utf-8")

    def replace(match: re.Match[str]) -> str:
        name = match.group(1)
        child = ROOT / (name if name.endswith(".tex") else name + ".tex")
        body = expand(child, ancestors + (path,))
        return (f"% BEGIN INCLUDED SOURCE: {name}\n"
                + body + f"\n% END INCLUDED SOURCE: {name}\n")

    return re.sub(r"\\input\{([^}]+)\}", replace, text)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tex-only", action="store_true")
    args = parser.parse_args()
    standalone = ROOT / (STEM + ".tex")
    standalone.write_text(expand(ROOT / "article.tex"), encoding="utf-8")
    print(f"Wrote {standalone.name}", flush=True)
    if args.tex_only:
        return
    if not shutil.which("pdflatex"):
        raise SystemExit("pdflatex is required to build the PDF.")
    build = ROOT / "build"
    build.mkdir(exist_ok=True)
    command = ["pdflatex", "-interaction=nonstopmode", "-halt-on-error",
               "-file-line-error", "-output-directory=" + str(build),
               str(standalone)]
    for pass_number in (1, 2, 3):
        run = subprocess.run(command, cwd=ROOT, text=True,
                             stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (build / f"pdflatex-pass-{pass_number}.txt").write_text(run.stdout)
        if run.returncode:
            print(run.stdout[-10000:])
            raise SystemExit(run.returncode)
    log = (build / (STEM + ".log")).read_text(errors="replace")
    problems = [line for line in log.splitlines()
                if ("Overfull " in line or "undefined" in line.lower()
                    or "multiply defined" in line.lower())]
    if problems:
        print("\n".join(problems))
        raise SystemExit("The PDF built, but its layout/reference gate failed.")
    destination = ROOT / (STEM + ".pdf")
    shutil.copy2(build / (STEM + ".pdf"), destination)
    print(f"Wrote {destination.name}; no overfull boxes or unresolved references.")


if __name__ == "__main__":
    main()
