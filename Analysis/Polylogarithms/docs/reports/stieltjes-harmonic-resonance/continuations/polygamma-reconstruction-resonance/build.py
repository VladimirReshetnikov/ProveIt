#!/usr/bin/env python3
"""Build the article and regenerate the portable single-file TeX source.

Requires a TeX installation containing the standard packages in article.tex.
No network, downloaded fonts, images, or bibliography processor are needed.
Run `python build.py`; pass --standalone to compile the flattened source.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
STEM = "Polygamma_Reconstruction_and_Resonance"


def flatten(path):
    content = path.read_text(encoding="utf-8")
    def include(match):
        child = (path.parent/match.group(1)).with_suffix(".tex")
        return ("\n% BEGIN " + str(child.relative_to(ROOT)) + "\n"
                + flatten(child) + "\n% END " + str(child.relative_to(ROOT)) + "\n")
    return re.sub(r"\\input\{([^}]+)\}", include, content)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--standalone", action="store_true")
    parser.add_argument("--tex-only", action="store_true")
    args = parser.parse_args()
    standalone = ROOT/(STEM+".tex")
    standalone.write_text(flatten(ROOT/"article.tex"), encoding="utf-8")
    if args.tex_only:
        print(standalone.name)
        return
    engine = shutil.which("pdflatex")
    if not engine:
        raise SystemExit("pdflatex is required. Install TeX Live or MiKTeX, then retry.")
    output = ROOT/".build"
    output.mkdir(exist_ok=True)
    source = standalone if args.standalone else ROOT/"article.tex"
    for repeat in range(3):
        command = [engine, "-interaction=nonstopmode", "-halt-on-error",
                   "-file-line-error", "-output-directory="+str(output), source.name]
        result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT)
        (output/f"pass_{repeat+1}.txt").write_text(result.stdout, encoding="utf-8")
        if result.returncode:
            print(result.stdout[-6000:])
            raise SystemExit(result.returncode)
    log = (output/(source.stem+".log")).read_text(encoding="utf-8")
    problems = [line for line in log.splitlines() if any(marker in line for marker in
                ["Overfull", "undefined references", "undefined on input", "multiply defined"])]
    if problems:
        raise SystemExit("Build completed with unresolved layout/reference problems:\n"+"\n".join(problems))
    destination = ROOT/(STEM+".pdf")
    shutil.copy2(output/(source.stem+".pdf"), destination)
    page_match = re.search(r"Output written on .*?\((\d+) pages", log, flags=re.S)
    report = {"build_passed": True, "source": source.name,
              "pdf": destination.name, "pages": int(page_match.group(1)) if page_match else None,
              "pdf_sha256": hashlib.sha256(destination.read_bytes()).hexdigest(),
              "unresolved_references": False, "overfull_boxes": False,
              "engine": subprocess.run([engine, "--version"], stdout=subprocess.PIPE,
                                       text=True).stdout.splitlines()[0]}
    (ROOT/"BUILD_REPORT.json").write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
