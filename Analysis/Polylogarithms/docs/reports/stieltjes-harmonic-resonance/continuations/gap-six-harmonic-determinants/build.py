#!/usr/bin/env python3
"""Assemble the standalone TeX and compile the article without network access."""
from pathlib import Path
import re
import subprocess
import json
import time

ROOT=Path(__file__).resolve().parent
STEM="Gap_Six_Harmonic_Determinants_and_Stieltjes_Collisions"

def expand(path,stack=()):
    if path in stack:
        raise RuntimeError("Recursive TeX input")
    text=path.read_text()
    def replace(match):
        child=ROOT/match.group(1)
        if not child.suffix:
            child=child.with_suffix(".tex")
        return "% BEGIN "+str(child.relative_to(ROOT))+"\n"+expand(child,stack+(path,))+"\n% END "+str(child.relative_to(ROOT))+"\n"
    return re.sub(r"\\input\{([^}]+)\}",replace,text)

if __name__=="__main__":
    (ROOT/"results").mkdir(exist_ok=True)
    standalone=ROOT/(STEM+".tex")
    standalone.write_text(expand(ROOT/"article.tex"))
    records=[]
    for n in range(1,4):
        start=time.perf_counter()
        result=subprocess.run(["pdflatex","-interaction=nonstopmode","-halt-on-error",
                               "-file-line-error",standalone.name],cwd=ROOT,
                              stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        (ROOT/"results"/f"latex_pass_{n}.log").write_text(result.stdout)
        records.append({"pass":n,"exit_code":result.returncode,
                        "elapsed_seconds":round(time.perf_counter()-start,3)})
        if result.returncode:
            print(result.stdout[-12000:])
            raise SystemExit(result.returncode)
    report={"standalone_tex":standalone.name,"pdf":STEM+".pdf","passes":records,
            "shell_escape":False}
    (ROOT/"results"/"build_report.json").write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(report,indent=2))
