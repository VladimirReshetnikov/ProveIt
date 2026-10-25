#!/usr/bin/env python3
"""Parse printed TeX residuals independently and compare exact coefficients."""
from pathlib import Path
import json,re
ROOT=Path(__file__).resolve().parent

def need(ok,msg):
    if not ok:raise ValueError(msg)

def parse_poly(s):
    s=s.replace(r"\,", "").replace(" ","").replace("\n","")
    out={}
    for token in re.findall(r"[+-]?[^+-]+",s):
        sign=-1 if token.startswith("-") else 1
        t=token.lstrip("+-")
        coefficient=re.match(r"\d+",t)
        if coefficient:
            c=sign*int(coefficient.group());t=t[coefficient.end():]
        else:c=sign
        mon=[]
        while t:
            f=re.match(r"x_\{(\d+)\}(?:\^\{(\d+)\})?",t)
            need(f is not None,"Unexpected printed polynomial syntax: "+t)
            mon.extend([int(f.group(1))]*int(f.group(2) or 1));t=t[f.end():]
        m=tuple(sorted(mon));out[m]=out.get(m,0)+c
    return {m:c for m,c in out.items() if c}

def main():
    release=json.loads((ROOT/"RELEASE.json").read_text())
    e=json.loads((ROOT/release["main_equation_directory"]/"equation.json").read_text())
    text=(ROOT/"report/report.tex").read_text()
    blocks=re.findall(r"% BEGIN_Q (\d+)\n(.*?)% END_Q \1",text,re.S)
    need(len(blocks)==len(e["residuals"]),"Wrong printed residual census")
    for expected,(number,s) in zip(e["residuals"],blocks):
        j=int(number)
        s=s.replace(r"\begin{align*}","").replace(r"\end{align*}","")
        s=re.sub(r"Q_\{\d+\}=\{\}&","",s).replace(r"\\","").replace("&{}","")
        got=parse_poly(s)
        wanted={tuple(m):c for c,m in expected["terms"]}
        need(got==wanted,"Printed residual differs: "+str(j))
    print(json.dumps({"status":"PASS","printed_residuals":len(blocks),
                     "scope":"TeX polynomial syntax parsed independently and matched to every literal coefficient."}))

if __name__=="__main__":main()
