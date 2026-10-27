#!/usr/bin/env python3
"""Build the PDF from the delivered LaTeX; no network or shell escape."""
from pathlib import Path
import json
import re
import shutil
import subprocess
ROOT=Path(__file__).resolve().parent
def main():
    build=ROOT/"_build";build.mkdir(exist_ok=True)
    executable=shutil.which("pdflatex")
    if executable is None:raise RuntimeError("pdfLaTeX is required")
    for _ in range(3):
        p=subprocess.run([executable,"-no-shell-escape","-interaction=nonstopmode",
                          "-halt-on-error","-output-directory",str(build),"report.tex"],
                         cwd=ROOT,text=True,capture_output=True)
        if p.returncode:
            raise RuntimeError(p.stdout[-7000:]+p.stderr[-2000:])
    log=(build/"report.log").read_text(errors="replace")
    errors=[]
    if "Overfull " in log:errors.append("overfull box")
    if "There were undefined references" in log:errors.append("undefined references")
    if "There were undefined citations" in log:errors.append("undefined citations")
    if errors:raise RuntimeError(", ".join(errors)+"; inspect _build/report.log")
    shutil.copyfile(build/"report.pdf",ROOT/"report.pdf")
    pages=re.search(r"Output written on .*?\((\d+) pages?",log,re.S)
    result={"status":"passed","passes":3,"shell_escape":False,"overfull_boxes":0,
            "undefined_references":False,"pages":int(pages.group(1)) if pages else None}
    (ROOT/"results"/"build.json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result,indent=2))
if __name__=="__main__":main()
