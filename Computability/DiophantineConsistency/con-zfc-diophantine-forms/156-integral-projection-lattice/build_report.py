#!/usr/bin/env python3
"""Generate the complete standalone TeX and compile its PDF."""
from collections import Counter
from pathlib import Path
import argparse, json, shutil, subprocess, tempfile

ROOT = Path(__file__).resolve().parent
STEM = "ConZFC_Integral_Projection_Lattice"

def load(p):
    return json.loads((ROOT / p).read_text())

def term_tex(c, mon, first=False):
    counts = Counter(mon)
    atom = "".join("x_{" + str(v) + "}" +
                   ("^{" + str(e) + "}" if e != 1 else "")
                   for v,e in sorted(counts.items()))
    factor = str(abs(c)) if abs(c) != 1 or not atom else ""
    sign = "-" if c < 0 else ("" if first else "+")
    return sign + factor + atom

def residual_appendix():
    eq = load("gram/balanced/equation.json")
    lines = [r"\begingroup\footnotesize", r"\setlength{\jot}{3pt}",
             r"\begin{align*}"]
    for idx,row in enumerate(eq["residuals"]):
        chunks, current, width = [], [], 0
        # Estimate visible width, not the number of TeX characters.
        for j,(c,mon) in enumerate(row["terms"]):
            term = term_tex(c,mon,j == 0)
            estimate = 2 + (len(str(abs(c))) if abs(c) != 1 or not mon else 0)
            estimate += sum(4 + (2 if e > 1 else 0)
                            for e in Counter(mon).values())
            if current and width + estimate > 61:
                chunks.append("".join(current)); current=[]; width=0
            current.append(term); width += estimate
        if current: chunks.append("".join(current))
        for k,chunk in enumerate(chunks):
            prefix = "r_{" + str(idx) + "}&={}" if k == 0 else r"&\quad{}"
            end = r"\\[2pt]" if k == len(chunks)-1 else r"\\*"
            lines.append(prefix + chunk + end)
    lines.extend([r"\end{align*}", r"\endgroup"])
    return "\n".join(lines)

def results_table():
    rows = [
        ("Inspected old 240-variable form",240,177,21482,6144),
        (r"$S_{240}^{\rm bal}$: projected squares",240,177,5477,15107),
        (r"$S_{240}^{\rm low}$: projected squares",240,177,9217,4512),
        (r"$Q_{240}$: principal Gram form",240,177,5803,6404),
        (r"$H_{240}$: lower-height Gram form",240,177,9357,4160),
        (r"$F_{241}$: factorial-free projection",241,177,5141,7968),
    ]
    lines = [r"\begin{center}\small",
             r"\begin{tabular}{p{0.43\textwidth}rrrr}",
             r"\toprule",
             r"Equation & Variables & Residuals & Monomials & Height\\\midrule"]
    for label,n,m,k,h in rows:
        lines.append(f"{label} & {n} & {m} & {k:,} & {h:,}"+r"\\")
    lines += [r"\bottomrule",r"\end{tabular}",r"\end{center}"]
    return "\n".join(lines)

def render():
    template=(ROOT/"report/report_template.tex").read_text()
    text=template.replace("%%RESULTS_TABLE%%",results_table())
    text=text.replace("%%RESIDUAL_APPENDIX%%",residual_appendix())
    if "%%" in text:
        raise ValueError("Unexpanded template placeholder")
    return text

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--tex-only",action="store_true")
    p.add_argument("--check",action="store_true")
    args=p.parse_args()
    target=ROOT/(STEM+".tex")
    text=render()
    if args.check:
        if target.read_text()!=text: raise ValueError("Standalone TeX is stale")
        print(json.dumps({"status":"PASS","principal_residuals":177,
                          "standalone_tex_bytes":len(text.encode())}))
        return
    target.write_text(text)
    if args.tex_only:
        print(str(target)); return
    with tempfile.TemporaryDirectory(prefix="conzfc-report-") as tmp:
        work=Path(tmp)
        (work/(STEM+".tex")).write_text(text)
        for run in range(3):
            proc=subprocess.run(["pdflatex","-interaction=nonstopmode",
                                 "-halt-on-error",STEM+".tex"],
                                cwd=work,capture_output=True,text=True)
            (ROOT/"report"/f"build-{run+1}.log").write_text(proc.stdout)
            if proc.returncode:
                raise RuntimeError(proc.stdout[-12000:])
        log=(work/(STEM+".log")).read_text(errors="replace")
        (ROOT/"report/tex-build.log").write_text(log)
        shutil.copyfile(work/(STEM+".pdf"),ROOT/(STEM+".pdf"))
    print(str(ROOT/(STEM+".pdf")))

if __name__=="__main__":
    main()
