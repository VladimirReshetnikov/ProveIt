#!/usr/bin/env python3
"""Assemble a standalone TeX article and compile its PDF.

Requires Python 3.10+ and latexmk with a standard TeX Live installation.
No network access or repository checkout is needed.
"""
from pathlib import Path
import argparse
import json
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
STEM = "Ordered_Boundary_Identities_and_Gamma_Kernels"
INPUT = re.compile(r"(?m)^\\input\{([^}]+)\}[ \t]*$")


def expand(path, active=()):
    path = path.resolve()
    if path in active:
        raise ValueError("Recursive TeX input: " + str(path))
    source = path.read_text(encoding="utf-8")

    def replace(match):
        name = match.group(1)
        child = path.parent / (name if name.endswith(".tex") else name + ".tex")
        return ("% Begin included source: " + name + "\n"
                + expand(child, active + (path,))
                + "\n% End included source: " + name)

    return INPUT.sub(replace, source)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--assemble-only", action="store_true")
    args = parser.parse_args()
    standalone = ROOT / (STEM + ".tex")
    standalone.write_text(
        "% Standalone assembly. Edit article.tex and sections/, then run build.py.\n"
        + expand(ROOT / "article.tex"), encoding="utf-8")
    if args.assemble_only:
        print(standalone)
        return
    if not shutil.which("latexmk"):
        raise SystemExit("latexmk is required; standalone TeX has been assembled.")
    build = ROOT / "build" / "latex"
    build.mkdir(parents=True, exist_ok=True)
    command = ["latexmk", "-pdf", "-interaction=nonstopmode", "-halt-on-error",
               "-outdir=" + str(build), standalone.name]
    completed = subprocess.run(command, cwd=ROOT, text=True,
                               stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (build / "compiler_output.txt").write_text(completed.stdout, encoding="utf-8")
    if completed.returncode:
        print(completed.stdout[-10000:])
        raise SystemExit(completed.returncode)
    log = (build / (STEM + ".log")).read_text(errors="replace")
    errors = [line for line in log.splitlines()
              if ("Overfull" in line or "undefined" in line
                  or "LaTeX Warning:" in line or "pdfTeX warning" in line)]
    if errors:
        raise SystemExit("Final TeX log requires review:\n" + "\n".join(errors))
    pdf = ROOT / (STEM + ".pdf")
    shutil.copy2(build / (STEM + ".pdf"), pdf)
    evidence = ROOT / "evidence"
    evidence.mkdir(exist_ok=True)
    (evidence / "latex_build.log").write_text(log, encoding="utf-8")
    record = {
        "status": "compiled",
        "source": standalone.name,
        "pdf": pdf.name,
        "tex_warnings": errors,
        "underfull_box_count": log.count("Underfull"),
        "visual_review": "Separate review required after changes.",
    }
    (evidence / "build_report.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps(record, indent=2))


if __name__ == "__main__":
    main()
