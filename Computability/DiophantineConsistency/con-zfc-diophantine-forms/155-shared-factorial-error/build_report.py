#!/usr/bin/env python3
"""Build a self-contained TeX article and literal polynomial appendices."""
from pathlib import Path
from collections import Counter
import json, re, subprocess, sys

ROOT = Path(__file__).resolve().parent

PREAMBLE = r"""
\documentclass[11pt]{article}
\usepackage[a4paper,margin=24mm,headheight=15pt]{geometry}
\usepackage[T1]{fontenc}
\usepackage[utf8]{inputenc}
\usepackage{lmodern,amsmath,amssymb,amsthm,mathtools}
\usepackage{booktabs,longtable,array}
\usepackage{xcolor,hyperref,microtype,fancyhdr,enumitem}
\hypersetup{colorlinks=true,linkcolor=blue!45!black,urlcolor=blue!45!black,citecolor=blue!45!black,
pdftitle={Shared factorial errors in a Diophantine equation for Con(ZFC)},
pdfauthor={OpenAI ChatGPT, prepared for Vladimir Reshetnikov}}
\pagestyle{fancy}\fancyhf{}
\fancyhead[L]{\small Shared factorial errors and Diophantine consistency}
\fancyhead[R]{\small 25 October 2026}
\fancyfoot[C]{\thepage}
\setlength{\parskip}{5pt}\setlength{\parindent}{0pt}
\setlist{itemsep=3pt,topsep=4pt}
\allowdisplaybreaks[4]
\newtheorem{theorem}{Theorem}[section]
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{proposition}[theorem]{Proposition}
\newtheorem{corollary}[theorem]{Corollary}
\theoremstyle{definition}\newtheorem{definition}[theorem]{Definition}
\newcommand{\Z}{\mathbb Z}\newcommand{\N}{\mathbb N}
\newcommand{\Con}{\operatorname{Con}}\newcommand{\ZFC}{\mathrm{ZFC}}
\newcommand{\ZF}{\mathrm{ZF}}\newcommand{\Ccalc}{\mathsf C222}
\newcommand{\Gform}{\mathcal G}
\newcommand{\abs}[1]{\left|#1\right|}
"""

BIB = r"""
\begin{thebibliography}{9}\raggedright\small
\bibitem{repo}
V. Reshetnikov and ProveIt contributors, \emph{ProveIt}, inspected commit
\texttt{3ecd6a6cf53d47519228328567f45fb7ee9781d9}, 25 October 2026.
\url{https://github.com/VladimirReshetnikov/ProveIt/tree/3ecd6a6cf53d47519228328567f45fb7ee9781d9}.
\bibitem{common}
ProveIt incoming contribution, \emph{ConZFC Common Remainders Radix47},
25 October 2026. Retained 252-integer direct equation and proof closure.
\url{https://github.com/VladimirReshetnikov/ProveIt/blob/3ecd6a6cf53d47519228328567f45fb7ee9781d9/docs/incoming/ConZFC_Common_Remainders_Radix47_2026-10-25.zip}.
\bibitem{centered}
ProveIt incoming contribution, \emph{ConZFC Centered Residues},
25 October 2026. Source of the odd-square radix predecessor and the
inspected compact 75/626, 76/464, and 77/460 points.
\url{https://github.com/VladimirReshetnikov/ProveIt/blob/3ecd6a6cf53d47519228328567f45fb7ee9781d9/docs/incoming/ConZFC_Centered_Residues_2026-10-25.zip}.
\bibitem{symmetric}
ProveIt incoming contribution, \emph{ConZFC Symmetric Remainders},
25 October 2026. The deterministic-center proof is retained; its
selected-nine orientation optimization is not used here.
\url{https://github.com/VladimirReshetnikov/ProveIt/blob/3ecd6a6cf53d47519228328567f45fb7ee9781d9/docs/incoming/ConZFC_Symmetric_Remainders_2026-10-25.zip}.
\bibitem{residual}
ProveIt incoming contribution, \emph{ConZFC Residual Bases and Denominator
Engineering}, 25 October 2026. Source of the compared affine-exposure
and residual-basis methodology.
\url{https://github.com/VladimirReshetnikov/ProveIt/blob/3ecd6a6cf53d47519228328567f45fb7ee9781d9/docs/incoming/ConZFC_Residual_Bases_Denominator_Engineering_2026-10-25.zip}.
\bibitem{overview}
ProveIt, \emph{Con(ZFC) in Diophantine form}, collection overview,
and \emph{Later arrivals and current size reductions}, active review,
at the inspected commit. Counts are compared in their stated domains.
\url{https://github.com/VladimirReshetnikov/ProveIt/tree/3ecd6a6cf53d47519228328567f45fb7ee9781d9/Computability/DiophantineConsistency}.
\end{thebibliography}
"""

def esc(s):
    return s.replace("\\",r"\textbackslash{}").replace("_",r"\_").replace("%",r"\%").replace("&",r"\&")

def term(c, m, first):
    sign = ("-" if c < 0 else ("" if first else "+"))
    factors = []
    for i, p in sorted(Counter(m).items()):
        factors.append("x_{%d}"%i + ("^{%d}"%p if p != 1 else ""))
    a = abs(c)
    coefficient = str(a) if a != 1 or not factors else ""
    return sign + coefficient + ("\\," if coefficient and factors else "") + "\\,".join(factors)

def row_latex(j, row):
    chunks=[]; cur=""; weight=0
    for k,(c,m) in enumerate(row["terms"]):
        t=term(c,m,k==0)
        w=3+len(str(abs(c)))+7*len(set(m))+sum(2 for z in Counter(m).values() if z>1)
        if cur and weight+w>86:
            chunks.append(cur);cur=t;weight=w
        else:
            cur+=t;weight+=w
    if cur:chunks.append(cur)
    out=["%% BEGIN_Q %d"%j,r"\begin{align*}",r"Q_{%d}={}&"%j+chunks[0]]
    out += [r"\\ &{}"+x for x in chunks[1:]]
    out += [r"\end{align*}","%% END_Q %d"%j]
    return "\n".join(out)

def main():
    release=json.loads((ROOT/"RELEASE.json").read_text())
    endpoint=ROOT/release["main_equation_directory"]
    e=json.loads((endpoint/"equation.json").read_text())
    m=json.loads((endpoint/"METRICS.json").read_text())
    n=m["variables"]; nr=m["rows"]
    macro_values={"MainVars":n,"MainLast":n-1,"MainRows":nr,"MainRowLast":nr-1,
                  "MainTerms":m["monomials"],"MainHeight":m["height"],
                  "MainDir":esc(endpoint.relative_to(ROOT/"equations").as_posix())}
    macros="\n".join("\\newcommand{\\%s}{%s}"%(k,v) for k,v in macro_values.items())
    intro = r"""
\title{\textbf{Shared factorial errors in a Diophantine equation for
\(\Con(\ZFC)\)}\\[5pt]\large A direct quartic with \MainVars{} unrestricted
integer unknowns}
\author{Prepared for Vladimir Reshetnikov and the ProveIt project\\
\small Mathematical development and computational assistance: OpenAI ChatGPT}
\date{25 October 2026}
\begin{document}\maketitle
\begin{abstract}
We give a completely specified degree-four polynomial in \MainVars{}
unrestricted integer unknowns whose lack of integer zeros is provably
equivalent in ZFC to \(\Con(\ZFC)\). The final equation has \MainRows{}
quadratic residuals, \MainTerms{} collected monomials, and coefficient
height \MainHeight{}. Every residual is printed in this report.

The main mathematical change shares one norm certificate between eleven
modular digit remainders and a signed factorial approximation error.
A nearest-integer factorial lemma recovers the intended factorial after
binomial extraction, making two former positivity certificates unnecessary.
Centered digits also allow an initially signed odd radix, whose positivity
is recovered later. The original beta-spacing formula is retained.
These changes give a 244-variable direct core; exact integral elimination
and reversible residual-row operations produce the stated final equation.

The route uses the numerical proof calculus C222 and its identified ZF/ZFC
refutation calibration, without instantiating K215 or Jones's universal
polynomial. We distinguish ordinary unbounded proofs from finite algebra
checks. No global simplicity minimum, consistency proof, or newly completed
end-to-end proof-assistant formalization is claimed.
\end{abstract}
\newpage\tableofcontents\newpage
"""
    body=(ROOT/"report/paper_main.tex").read_text()
    app=[
      r"\appendix",
      r"\section{The complete residual list}\label{app:residuals}",
      r"The variables \(x_0,\ldots,x_{\MainLast}\) range independently over \(\Z\).",
      r"The entire equation is \(P=\sum_{j=0}^{\MainRowLast}Q_j^2=0\).",
      r"The following list is generated from the literal JSON and independently parsed back into its exact integer coefficient data. Each monomial coefficient is literal. There are no additional quantified registers.",
      r"\begingroup\small\setlength{\jot}{1pt}",
    ]
    app += [row_latex(i,r) for i,r in enumerate(e["residuals"])]
    app += [r"\endgroup",r"\section{Coordinate names and artifact interpretation}"]
    app += [r"The semantic names below describe the restored graph coordinates; the equation itself uses only the independent \(x_i\). Recorded translation shifts must be applied before identifying an actual source quantity with a final coordinate. The names are annotations, not new equations.",
            r"\begingroup\footnotesize\renewcommand{\arraystretch}{0.96}",r"\begin{longtable}{r >{\raggedright\arraybackslash}p{0.38\textwidth} r >{\raggedright\arraybackslash}p{0.38\textwidth}}",
            r"\toprule Index & Source name & Index & Source name\\\midrule\endhead"]
    half=(n+1)//2
    for i in range(half):
        j=i+half
        left="%d & \\path{%s}"%(i,e["variables"][i]["name"])
        right=("%d & \\path{%s}"%(j,e["variables"][j]["name"])) if j<n else "&"
        app.append(left+" & "+right+r"\\")
    app += [r"\bottomrule\end{longtable}\endgroup",r"\end{document}"]
    text=PREAMBLE+macros+intro+body+BIB+"\n".join(app)+"\n"
    out=ROOT/"report/report.tex";out.write_text(text)
    if "--tex-only" not in sys.argv:
        for _ in range(3):
            p=subprocess.run(["pdflatex","-interaction=nonstopmode","-halt-on-error","report.tex"],
                             cwd=out.parent,capture_output=True,text=True)
            (out.parent/"last_build_output.txt").write_text(p.stdout+p.stderr)
            if p.returncode:
                print((p.stdout+p.stderr)[-7000:]);raise SystemExit(p.returncode)
    print(json.dumps({"tex":str(out),"variables":n,"residuals":nr,"status":"BUILT"}))

if __name__=="__main__":main()
