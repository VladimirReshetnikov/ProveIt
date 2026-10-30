"""Render the separate 86-gate presentation from the pinned JSON and fixed data."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent;D=HERE.parents[1];raw=(HERE/'candidate.json').read_bytes();assert hashlib.sha256(raw).hexdigest()=='e9889a81a491b85491dde749e82158109ea98ff94ed41fc0f05dc810ec58b91f';j=json.loads(raw);old=(D/'equation.tex').read_text();constants=old[old.index('\\textbf{The four fixed integers.}'):old.index('\\endgroup',old.index('\\textbf{The integer $\\mathcal A$'))+len('\\endgroup')]
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
{\small Positive integer unknowns; an 86-operation evaluator.}
\end{center}\vspace{-8pt}
\begin{multicols}{2}
\fontsize{8.6}{9.1}\selectfont
'''
footer=r'''
\normalfont\fontsize{7.7}{8.2}\selectfont
The fixed integer $\mathcal A$ above is written in base 10. A Lean theorem
establishes the existence of an HA derivation of both directions between
this no-solution sentence and the formalized consistency of ZFC. The theorem
was independently replayed on a checked pre-merge source snapshot; historical
HA, ZF, Foundation and package inputs remain inherited boundaries. A later
source refresh is in progress. The circuit count is not a minimality or degree
claim.
\end{multicols}
\clearpage
\begin{center}{\large\bfseries Exact 86-operation circuit}\end{center}
Each numbered line defines one gate over the integers; the inputs are the
thirteen unknowns and the four fixed integers above. The circuit uses the
ASCII names \texttt{alpha, xi, eta, zeta, upsilon, gamma, beta, mu, omega,}
\texttt{ell, Delta} for their displayed counterparts; \texttt{g} is the
unknown named $g$. Its last gate is zero
exactly when the displayed equation holds. Intermediate gate names below are
local names, not additional unknowns.
\begin{multicols}{3}
\raggedright\ttfamily\fontsize{7.2}{8.4}\selectfont
'''
mapname={'alpha':'alpha','eta':'eta','zeta':'zeta','gamma':'gamma','r':'xi','i':'g','y':'upsilon','beta':'beta','K0':'K','MC':'mu','MF':'omega','qm':'b','Bt':'W','b0':'L','Dstar':'D','G':'rankseed','F0':'first','F1':'main','Fa':'aux','Fs':'strong','P13':'P'}
def fmt(x):return mapname.get(str(x),str(x)).replace('_',r'\_')
lines=[]
for idx,(name,op,a,b) in enumerate(j['source'],1):lines.append(f'{idx}. {fmt(name)} = {fmt(a)} {op} {fmt(b)}\\\\')
assert len(lines)==86
result=header+(HERE/'equation86-display.tex').read_text()+constants+footer+'\n'.join(lines)+r'''
\end{multicols}
\end{document}
'''
(D/'equation86.tex').write_text(result)
print('generated',D/'equation86.tex','with',len(lines),'gates; candidate SHA256',hashlib.sha256(raw).hexdigest())
