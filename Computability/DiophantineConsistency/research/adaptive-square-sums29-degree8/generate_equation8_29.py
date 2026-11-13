#!/usr/bin/env python3
"""Generate the degree-8 presentation from its pinned circuit and fixed block."""
import hashlib
import json
from pathlib import Path
D=Path(__file__).resolve().parent
ROOT=D.parents[1]
raw=(D/'candidate.json').read_bytes()
if hashlib.sha256(raw).hexdigest()!='894ff6fa3205629c03de826d8984f4959c2be317bf61c46d0f393f770d113a20':
    raise RuntimeError('candidate mismatch')
j=json.loads(raw)
old=(ROOT/'equation.tex').read_text()
start=old.index(r'\textbf{The four fixed integers.}')
end=old.index(r'\endgroup',old.index(r'\textbf{The integer $\mathcal A$'))+len(r'\endgroup')
constants=old[start:end]
header=r'''\documentclass[10pt]{article}
\usepackage[letterpaper,margin=.38in]{geometry}
\usepackage{amsmath,amssymb,multicol,graphicx}
\pdfinfoomitdate=1\pdftrailerid{}
\pagestyle{empty}\setlength{\parindent}{0pt}\setlength{\parskip}{2pt}
\setlength{\columnsep}{13pt}\setlength{\jot}{0pt}
\setlength{\abovedisplayskip}{3pt}\setlength{\belowdisplayskip}{3pt}
\let\bigsum\sum\renewcommand{\sum}{\bigsum\nolimits}
\newcommand{\fl}[1]{\left\lfloor#1\right\rfloor}
\newcommand{\rg}[2]{\{#1,\ldots,#2\}}
\begin{document}
\begin{center}
{\large\bfseries A twenty-nine-variable candidate equation}\\[-1pt]
{\small Positive integer unknowns; exact degree 8; a 135-operation evaluator.}
\end{center}\vspace{-8pt}
\begin{multicols}{2}
\fontsize{8.6}{9.1}\selectfont
'''
footer=r'''
\normalfont\fontsize{7.7}{8.2}\selectfont
The fixed integer $\mathcal A$ above is written in base 10. This equation is a candidate: its model witness transport has been checked,
but its native intuitionistic PRA equivalence has not passed a paired guarded replay. Its exact degree is certified by integer-polynomial calculations;
the 135-operation count is for the unshifted circuit. Neither count is a
minimality claim.
\end{multicols}
\clearpage
\begin{center}{\large\bfseries Exact 135-operation circuit}\end{center}
Each numbered line defines one gate over the integers. The inputs are the
twenty-nine unknowns and the four fixed integers above. The ASCII names
\texttt{alpha, xi, eta, zeta, upsilon, gamma, vartheta, psi, varphi, epsilon, beta, mu, omega, ell, Delta, delta, kappa, lambda, sigma, tau, chi, theta, nu}
refer to their displayed counterparts; \texttt{g} is the unknown $g$. The last
gate is zero exactly when the displayed equation holds. The circuit inputs
\texttt{cNamed, ellNamed} are $c,\ell$; gate \texttt{a} is the displayed abbreviation; gate \texttt{WComputed} is the displayed abbreviation $W=C(X+Kq)-Fq$, and gate \texttt{m} is $m=f^2$. The inputs
\texttt{n, Z, D, V, delta} are the displayed
$n,Z,D,V,\delta$; \texttt{kappa, lambda, tau, chi, theta, Q}
are $\kappa,\lambda,\tau,\chi,\theta,Q$. Gates \texttt{q3, g55, g39, y2, g80} compute $s,x,\sigma,\nu,\vartheta$. Gates \texttt{E, I} compute
$XY,ng$; the display uses $E=\lambda$, $I=\theta$. Intermediate gate
names below are local abbreviations, not additional unknowns.
\begin{multicols}{3}
\raggedright\ttfamily\fontsize{7.2}{8.4}\selectfont
'''
rename={'r':'xi','i':'g','y':'upsilon','K0':'K','MC':'mu','MF':'omega',
        'qm':'b','Bt':'WComputed','b0':'L','Dstar':'D','G':'rankseed','squareVariable':'vartheta','scaleVariable':'psi','mainScaleVariable':'varphi','rankVariable':'epsilon','cVariable':'cNamed','aVariable':'aNamed','ellVariable':'ellNamed','wValueVariable':'WNamed','cubeVariable':'s','productVariable':'x','f2':'m','cSquareVariable':'n','zValueVariable':'Z','dValueVariable':'D','vValueVariable':'V','deltaVariable':'delta','qSquareVariable':'kappa','productVariable2':'lambda','psiSquareVariable':'sigma','ellProductVariable':'tau','varphiSquareVariable':'chi','scaledIndexVariable':'theta','ySquareVariable':'nu','qValueVariable':'Q','rankDifference':'rankDiff','rankConstraint':'rankCheck','finalWithRank':'result17','mainScaleDifference':'mainDiff','mainScaleConstraint':'mainCheck','finalWithMainScale':'result16','scaleDifference':'scaleDiff','scaleConstraint':'scaleCheck','finalWithScale':'final','squareConstraint':'constraint','squareDifference':'difference','sumWithConstraint':'result'}
def fmt(x):return rename.get(str(x),str(x)).replace('_',r'\_')
lines=[f'{i}. {fmt(name)} = {fmt(a)} {op} {fmt(b)}'+r'\\'
       for i,(name,op,a,b) in enumerate(j['source'],1)]
if len(lines)!=135:raise RuntimeError('circuit count')
result=header+(D/'equation8-29-display.tex').read_text()+constants+footer+'\n'.join(lines)+r'''
\end{multicols}
\end{document}
'''
(ROOT/'equation8-29.tex').write_text(result)
print('PASS degree-8 TeX, 135 gates, candidate',hashlib.sha256(raw).hexdigest())
