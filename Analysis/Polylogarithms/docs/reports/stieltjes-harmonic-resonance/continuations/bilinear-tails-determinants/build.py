#!/usr/bin/env python3
"""Flatten the modular article and optionally build its PDF with latexmk."""
import argparse
from pathlib import Path
import re
import shutil
import subprocess

ROOT=Path(__file__).resolve().parent
STEM="Bilinear_Tails_and_Harmonic_Determinants"


def flatten(path, stack=()):
    path=path.resolve()
    if path in stack:
        raise ValueError(f"Cyclic TeX input: {path.name}")
    text=path.read_text(encoding="utf-8")
    def replace(match):
        child=ROOT/match.group(1)
        if child.suffix != ".tex":
            child=child.with_suffix(".tex")
        return ("% BEGIN "+str(child.relative_to(ROOT))+"\n"
                +flatten(child,stack+(path,))+"\n% END "
                +str(child.relative_to(ROOT))+"\n")
    return re.sub(r"\\input\{([^}]+)\}",replace,text)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pdf",action="store_true",help="also typeset with latexmk")
    args=parser.parse_args()
    tex=ROOT/(STEM+".tex")
    tex.write_text(flatten(ROOT/"article.tex"),encoding="utf-8")
    print(f"Wrote {tex.name}",flush=True)
    if args.pdf:
        build=ROOT/"build"
        build.mkdir(exist_ok=True)
        subprocess.run(["latexmk","-pdf","-interaction=nonstopmode",
                        "-halt-on-error","-file-line-error","-outdir=build",tex.name],
                       cwd=ROOT,check=True)
        shutil.copy2(build/(STEM+".pdf"),ROOT/(STEM+".pdf"))
        print(f"Wrote {STEM}.pdf",flush=True)


if __name__=="__main__":
    main()
