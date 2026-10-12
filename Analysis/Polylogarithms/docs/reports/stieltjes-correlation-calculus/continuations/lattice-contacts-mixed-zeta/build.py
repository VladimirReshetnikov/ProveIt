#!/usr/bin/env python3
"""Assemble the standalone TeX and compile its PDF. Standard library only."""
from pathlib import Path
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
STEM = "Lattice_Contacts_and_Mixed_Zeta_Identities"


def expand(path, stack=()):
    path = path.resolve()
    if path in stack or not path.is_relative_to(ROOT):
        raise ValueError(f"Unsafe or cyclic input: {path}")
    text = path.read_text(encoding="utf-8")
    def replace(match):
        child = path.parent / match.group(1)
        if not child.suffix:
            child = child.with_suffix(".tex")
        return "\n% BEGIN " + str(child.relative_to(ROOT)) + "\n" + expand(child, stack + (path,)) + "\n% END INPUT\n"
    return re.sub(r"\\input\{([^}]+)\}", replace, text)


def main():
    target = ROOT / f"{STEM}.tex"
    target.write_text("% Standalone source assembled by build.py.\n" + expand(ROOT / "article.tex"), encoding="utf-8")
    logs = ROOT / "build"
    logs.mkdir(exist_ok=True)
    if shutil.which("latexmk"):
        commands = [["latexmk", "-pdf", "-interaction=nonstopmode", "-halt-on-error", "-file-line-error", target.name]]
    else:
        commands = [["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "-file-line-error", target.name]] * 3
    with (logs / "latex_console.txt").open("w") as log:
        for command in commands:
            subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, check=True)
    texlog = target.with_suffix(".log").read_text(errors="replace")
    forbidden = ["Overfull ", "There were undefined references", "multiply defined", "Fatal error"]
    defects = [s for s in forbidden if s in texlog]
    if defects:
        raise RuntimeError("Inspect TeX log before delivery: " + ", ".join(defects))
    shutil.copy2(target.with_suffix(".log"), logs / "latex.log")
    print(f"Created {target.name} and {STEM}.pdf")


if __name__ == "__main__":
    main()

