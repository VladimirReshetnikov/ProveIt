#!/usr/bin/env python3
"""Build the article and its standalone source; fail on unresolved/overflow warnings."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[1]
MAIN=ROOT/"polylogarithms_finite_parts.tex"
STANDALONE=ROOT/"article_standalone.tex"
VERIFY=ROOT/"verification"

def expand(path,seen=()):
    path=path.resolve()
    if path in seen:
        raise ValueError("Circular TeX input: "+str(path))
    source=path.read_text()
    def include(match):
        child=path.parent/match.group(1)
        if not child.suffix: child=child.with_suffix(".tex")
        return "\n% BEGIN "+child.relative_to(ROOT).as_posix()+"\n"+expand(child,seen+(path,))+"\n% END input\n"
    return re.sub(r"\\input\{([^}]+)\}",include,source)

def main():
    STANDALONE.write_text("% Standalone expansion; regenerate with python3 code/build_article.py\n"+expand(MAIN))
    command=["latexmk","-pdf","-interaction=nonstopmode","-halt-on-error",MAIN.name]
    process=subprocess.run(command,cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    VERIFY.mkdir(exist_ok=True)
    (VERIFY/"build_console.log").write_text(process.stdout)
    logfile=MAIN.with_suffix(".log")
    log=logfile.read_text(errors="replace") if logfile.exists() else process.stdout
    flags=[]
    for pattern,name in [
        (r"(?:Citation|Reference)\s+.*?undefined","unresolved_reference_or_citation"),
        (r"There were undefined references","undefined_references"),
        (r"Overfull \\[hv]box","overfull_box"),
        (r"Label\(s\) may have changed","unstable_references"),
        (r"multiply defined","duplicate_labels")
    ]:
        if re.search(pattern,log,re.S if name=="unresolved_reference_or_citation" else 0):
            flags.append(name)
    info=subprocess.run(["pdfinfo",str(MAIN.with_suffix(".pdf"))],text=True,capture_output=True)
    pages=re.search(r"^Pages:\s+(\d+)",info.stdout,re.M)
    versions={}
    for name,cmd in [("pdflatex",["pdflatex","--version"]),("latexmk",["latexmk","-v"])]:
        v=subprocess.run(cmd,text=True,capture_output=True)
        versions[name]=v.stdout.splitlines()[:2]
    report={
        "status":"passed" if process.returncode==0 and not flags and pages else "failed",
        "command":command,"returncode":process.returncode,"flags":flags,
        "pdf_pages":int(pages.group(1)) if pages else None,
        "pdf_sha256":hashlib.sha256(MAIN.with_suffix(".pdf").read_bytes()).hexdigest() if MAIN.with_suffix(".pdf").exists() else None,
        "standalone_source":STANDALONE.name,"versions":versions,
        "visual_review":"Recorded separately in pdf_review.json"
    }
    (VERIFY/"build_status.json").write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(report,indent=2))
    if report["status"]!="passed":
        print("Inspect verification/build_console.log and the TeX log.",file=sys.stderr)
        return 1
    return 0

if __name__=="__main__":
    raise SystemExit(main())

