#!/usr/bin/env python3
"""Compile the manuscript, with an optional local TeX Live bootstrap.

Usage: python3 build.py [--checks]
No system files are modified. A normal working pdfLaTeX installation is
preferred. The fallback handles an installed TeX Live tree whose filename
databases, format and font map have not been initialized.
"""
from pathlib import Path
import argparse
import json
import os
import shutil
import subprocess
import sys

ROOT=Path(__file__).resolve().parent


def run(argv,env,logpath):
    p=subprocess.run(argv,cwd=ROOT,env=env,text=True,stdout=subprocess.PIPE,
                     stderr=subprocess.STDOUT)
    logpath.write_text(p.stdout)
    if p.returncode:
        print(p.stdout[-6000:])
        raise SystemExit(p.returncode)
    return p.stdout


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--checks",action="store_true",
                        help="also rerun exact geometry and the optional numerical model")
    args=parser.parse_args()
    cache=ROOT/"build_cache"; cache.mkdir(exist_ok=True)
    env=os.environ.copy()
    engine=shutil.which("pdflatex")
    if not engine:
        raise SystemExit("pdfLaTeX is required (TeX Live or MiKTeX).")
    kpse=shutil.which("kpsewhich")
    located=""
    if kpse:
        located=subprocess.run([kpse,"-format=fmt","pdflatex.fmt"],env=env,
                               text=True,stdout=subprocess.PIPE).stdout.strip()
    bootstrap=False
    if not located:
        trees=[Path("/usr/share/texlive/texmf-dist"),Path("/usr/share/texmf")]
        if not (trees[0]/"tex/latex/base/latex.ltx").exists():
            raise SystemExit("No initialized pdfLaTeX format; initialize your TeX installation.")
        bootstrap=True
        env["TEXMF"]="{"+",".join(str(p) for p in trees if p.exists())+"}"
        env["TEXFORMATS"]=str(cache)+os.pathsep
        env["TEXFONTMAPS"]=str(cache)+os.pathsep
        maps=[trees[1]/"fonts/map/dvips/lm/lm.map"]
        maps+=sorted((trees[0]/"fonts/map/dvips/amsfonts").glob("*.map"))
        (cache/"pdftex.map").write_text("\n".join(p.read_text() for p in maps if p.exists()))
        if not (cache/"pdflatex.fmt").exists():
            pdftex=shutil.which("pdftex")
            if not pdftex:
                raise SystemExit("The local fallback also requires pdftex.")
            run([pdftex,"-ini","-etex","-interaction=nonstopmode","-halt-on-error",
                 "-jobname=pdflatex","-progname=pdflatex",
                 "-output-directory="+str(cache),"pdflatex.ini"],
                env,cache/"format_build.log")
    check_results=[]
    if args.checks:
        for script in ["verify_geometry.py","continuum_model.py"]:
            run([sys.executable,str(ROOT/"verification"/script)],env,
                cache/(script+".log"))
            check_results.append({"script":script,"exit_code":0})
    for iteration in range(1,4):
        output=run([engine,"-interaction=nonstopmode","-halt-on-error",
                    "prime_scale_coalescence.tex"],env,
                   cache/("latex_pass_"+str(iteration)+".log"))
    warnings=[line for line in output.splitlines()
              if any(k in line for k in ["Overfull","undefined","Warning:"])]
    report={"status":"success","engine":"pdfLaTeX",
            "local_format_bootstrap":bootstrap,"passes":3,
            "warnings":warnings,"checks":check_results,
            "pdf":"prime_scale_coalescence.pdf"}
    (ROOT/"provenance"/"build_report.json").write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(report,indent=2))


if __name__=="__main__":
    main()
