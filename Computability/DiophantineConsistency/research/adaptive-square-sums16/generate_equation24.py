#!/usr/bin/env python3
"""Generate the degree-24 presentation from its pinned circuit and fixed block."""
import hashlib
import json
from pathlib import Path
D=Path(__file__).resolve().parent
ROOT=D.parents[1]
raw=(D/'candidate.json').read_bytes()
if hashlib.sha256(raw).hexdigest()!='bfb13952920a218bb13b168006f19d2d1a29eaf184077cee319cf323472d44cc':
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
{\large\bfseries A sixteen-variable consistency equation}\\[-1pt]
{\small Positive integer unknowns; exact degree 24; a 96-operation evaluator.}
\end{center}\vspace{-8pt}
\begin{multicols}{2}
\fontsize{8.6}{9.1}\selectfont
'''
footer=r'''
\normalfont\fontsize{7.7}{8.2}\selectfont
The fixed integer $\mathcal A$ above is written in base 10. Lean proves that
the formalized equation has no positive solution exactly when the chosen
arithmetized ZFC consistency statement holds, by a derivation in the specified
intuitionistic PRA. The literal endpoint was independently replayed on a fixed
source snapshot; some transitive dependencies remain inherited. The exact
degree is certified by integer-polynomial calculations. The 96-operation count
is for the unshifted circuit; neither count is a minimality claim.
\end{multicols}
\clearpage
\begin{center}{\large\bfseries Exact 96-operation circuit}\end{center}
Each numbered line defines one gate over the integers. The inputs are the
sixteen unknowns and the four fixed integers above. The ASCII names
\texttt{alpha, xi, eta, zeta, upsilon, gamma, vartheta, psi, varphi, beta, mu, omega, ell, Delta}
refer to their displayed counterparts; \texttt{g} is the unknown $g$. The last
gate is zero exactly when the displayed equation holds. Intermediate gate
names below are local abbreviations, not additional unknowns.
\begin{multicols}{3}
\raggedright\ttfamily\fontsize{7.2}{8.4}\selectfont
'''
rename={'r':'xi','i':'g','y':'upsilon','K0':'K','MC':'mu','MF':'omega',
        'qm':'b','Bt':'W','b0':'L','Dstar':'D','G':'rankseed','squareVariable':'vartheta','scaleVariable':'psi','mainScaleVariable':'varphi','mainScaleDifference':'mainDiff','mainScaleConstraint':'mainCheck','finalWithMainScale':'result16','scaleDifference':'scaleDiff','scaleConstraint':'scaleCheck','finalWithScale':'final','squareConstraint':'constraint','squareDifference':'difference','sumWithConstraint':'result'}
def fmt(x):return rename.get(str(x),str(x)).replace('_',r'\_')
lines=[f'{i}. {fmt(name)} = {fmt(a)} {op} {fmt(b)}'+r'\\'
       for i,(name,op,a,b) in enumerate(j['source'],1)]
if len(lines)!=96:raise RuntimeError('circuit count')
result=header+(D/'equation24-display.tex').read_text()+constants+footer+'\n'.join(lines)+r'''
\end{multicols}
\end{document}
'''
(ROOT/'equation24.tex').write_text(result)
print('PASS degree-24 TeX, 96 gates, candidate',hashlib.sha256(raw).hexdigest())
