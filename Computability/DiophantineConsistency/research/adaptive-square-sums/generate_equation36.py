#!/usr/bin/env python3
"""Generate the degree-36 presentation from its pinned circuit and fixed block."""
import hashlib
import json
from pathlib import Path
D=Path(__file__).resolve().parent
ROOT=D.parents[1]
raw=(D/'candidate.json').read_bytes()
if hashlib.sha256(raw).hexdigest()!='11fb3c192fb3a8ab9204ef0a5401198d986e002242e4f48442147aa356263828':
    raise RuntimeError('candidate mismatch')
j=json.loads(raw)
old=(ROOT/'equation.tex').read_text()
start=old.index(r'\textbf{The four fixed integers.}')
end=old.index(r'\endgroup',old.index(r'\textbf{The integer $\mathcal A$'))+len(r'\endgroup')
constants=old[start:end]
header=r'''\documentclass[10pt]{article}
\usepackage[letterpaper,margin=.38in]{geometry}
\usepackage{amsmath,amssymb,multicol}
\pdfinfoomitdate=1\pdftrailerid{}
\pagestyle{empty}\setlength{\parindent}{0pt}\setlength{\parskip}{2pt}
\setlength{\columnsep}{13pt}\setlength{\jot}{0pt}
\setlength{\abovedisplayskip}{3pt}\setlength{\belowdisplayskip}{3pt}
\let\bigsum\sum\renewcommand{\sum}{\bigsum\nolimits}
\newcommand{\fl}[1]{\left\lfloor#1\right\rfloor}
\newcommand{\rg}[2]{\{#1,\ldots,#2\}}
\begin{document}
\begin{center}
{\large\bfseries A thirteen-variable consistency equation}\\[-1pt]
{\small Positive integer unknowns; exact degree 36; an 87-operation evaluator.}
\end{center}\vspace{-8pt}
\begin{multicols}{2}
\fontsize{8.6}{9.1}\selectfont
'''
footer=r'''
\normalfont\fontsize{7.7}{8.2}\selectfont
The fixed integer $\mathcal A$ above is written in base 10. Lean proves that
this equation and the 86-operation equation have the same positive solutions
in every model used by the arithmetic proof. The construction of an
intuitionistic PRA proof of the consistency equivalence is in progress. The
exact degree is certified by integer-polynomial calculations. The 87-operation
count is for the unshifted circuit; neither count is a minimality claim.
\end{multicols}
\clearpage
\begin{center}{\large\bfseries Exact 87-operation circuit}\end{center}
Each numbered line defines one gate over the integers. The inputs are the
thirteen unknowns and the four fixed integers above. The ASCII names
\texttt{alpha, xi, eta, zeta, upsilon, gamma, beta, mu, omega, ell, Delta}
refer to their displayed counterparts; \texttt{g} is the unknown $g$. The last
gate is zero exactly when the displayed equation holds. Intermediate gate
names below are local abbreviations, not additional unknowns.
\begin{multicols}{3}
\raggedright\ttfamily\fontsize{7.2}{8.4}\selectfont
'''
rename={'r':'xi','i':'g','y':'upsilon','K0':'K','MC':'mu','MF':'omega',
        'qm':'b','Bt':'W','b0':'L','Dstar':'D','G':'rankseed'}
def fmt(x):return rename.get(str(x),str(x)).replace('_',r'\_')
lines=[f'{i}. {fmt(name)} = {fmt(a)} {op} {fmt(b)}'+r'\\'
       for i,(name,op,a,b) in enumerate(j['source'],1)]
if len(lines)!=87:raise RuntimeError('circuit count')
result=header+(D/'equation36-display.tex').read_text()+constants+footer+'\n'.join(lines)+r'''
\end{multicols}
\end{document}
'''
(ROOT/'equation36.tex').write_text(result)
print('PASS degree-36 TeX, 87 gates, candidate',hashlib.sha256(raw).hexdigest())
