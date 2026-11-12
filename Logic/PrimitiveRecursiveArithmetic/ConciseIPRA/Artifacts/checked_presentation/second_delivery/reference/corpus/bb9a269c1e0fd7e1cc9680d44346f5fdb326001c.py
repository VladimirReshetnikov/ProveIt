"""Assemble the standalone LaTeX report from its editable fragments."""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent
HEADER = r'''\documentclass[11pt,letterpaper]{article}
\usepackage[T1]{fontenc}
\usepackage[utf8]{inputenc}
\usepackage{lmodern}
\usepackage[margin=0.9in,headheight=14pt]{geometry}
\usepackage{amsmath,amssymb,amsthm,mathtools}
\usepackage{booktabs,tabularx,array,longtable}
\usepackage{microtype,xcolor,listings,enumitem,fancyhdr}
\usepackage{xurl}
\usepackage{hyperref}
\definecolor{navy}{RGB}{29,57,82}
\definecolor{codegray}{RGB}{247,248,250}
\hypersetup{colorlinks=true,linkcolor=navy,citecolor=navy,urlcolor=navy,
 pdftitle={Parameter substitution is enough for iPRA},
 pdfauthor={Research note on the ConciseIPRA proposal}}
\setlength{\parskip}{0.4em}
\setlength{\parindent}{0pt}
\setlength{\emergencystretch}{2em}
\setlist{itemsep=0.25em,topsep=0.4em}
\renewcommand{\arraystretch}{1.15}
\pagestyle{fancy}
\fancyhf{}
\fancyhead[L]{\small Parameter substitution for iPRA}
\fancyhead[R]{\small Research note}
\fancyfoot[C]{\thepage}
\newtheorem{theorem}{Theorem}[section]
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{corollary}[theorem]{Corollary}
\lstset{language=Python,basicstyle=\ttfamily\scriptsize,
 columns=fullflexible,keepspaces=true,breaklines=true,
 showstringspaces=false,frame=single,framesep=5pt,
 backgroundcolor=\color{codegray},rulecolor=\color{black!20},
 xleftmargin=5pt,xrightmargin=5pt,aboveskip=0.8em,belowskip=0.8em}
\title{\textbf{Parameter substitution is enough for iPRA}\\[0.5em]
 \large A raw clause calculus and a complete proof checker}
\author{Research note on the ConciseIPRA proposal}
\date{November 12, 2026}
\begin{document}
\maketitle
\begin{abstract}
We give a raw presentation of intuitionistic primitive recursive arithmetic
whose primitive equality operation substitutes inside terms only at free
numerical variables. Equalities with compound sources are used only by
root composition or symmetry. A fresh-alias construction derives arbitrary
term-template transport, giving exact consequence equivalence with the
repository's native calculus and, through its established bridge,
whole-domain bi-interpretability with full first-order iPRA.
The complete checker uses five instruction families, including the two
explicit iterator computation equations, and has no primitive reflexivity
rule. In the strongest matched comparison it is 2857 rather than 2907
normalized bytes, with slightly larger token and AST counts.
The paper states every rule, proves both interpretation round trips,
supplies checked proof transformations, and distinguishes this local
simplification from an unproved global minimum.
\end{abstract}
\vfill
\noindent\textbf{Deliverable status:} written mathematical proof; executable
checker and proof translations; no newly claimed Lean or Rocq verification.
\newpage
\tableofcontents
\newpage
'''

BIBLIOGRAPHY = r'''
\begin{thebibliography}{9}
\raggedright
\bibitem{index}
Vladimir Reshetnikov and ProveIt contributors.
\emph{Concise presentations of intuitionistic primitive recursive arithmetic}.
Pinned commit \texttt{5d85023b0688e03b75f0ec3a04bb43ef0bb51705}.
\href{https://github.com/VladimirReshetnikov/ProveIt/blob/5d85023b0688e03b75f0ec3a04bb43ef0bb51705/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/README.md}{Project index and rule inventory}.

\bibitem{templatefree}
ProveIt, \emph{Template-free equality}, especially the optional
fresh-variable alias proof in
\texttt{Research/template\_free/evidence/global\_rewrite\_marker\_proof.md}.
\href{https://github.com/VladimirReshetnikov/ProveIt/blob/5d85023b0688e03b75f0ec3a04bb43ef0bb51705/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Research/template_free/evidence/global_rewrite_marker_proof.md}{Pinned proof note}.
An unchanged copy is included in the archive.

\bibitem{rawclausal}
ProveIt, \emph{Five rules for iPRA with ordinary substitution},
\texttt{Research/raw\_clausal}.
\href{https://github.com/VladimirReshetnikov/ProveIt/tree/5d85023b0688e03b75f0ec3a04bb43ef0bb51705/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Research/raw_clausal}{Pinned raw clause presentation}.
Its complete checker supplies the 3046-byte comparison and the inherited
positive example corpus.

\bibitem{nativebiinterp}
ProveIt Lean formalization,
\texttt{Lean/ConciseIPRA/NativeBiInterpretation.lean} and
\texttt{BiInterpretation.lean} at the pinned commit.
\href{https://github.com/VladimirReshetnikov/ProveIt/blob/5d85023b0688e03b75f0ec3a04bb43ef0bb51705/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/NativeBiInterpretation.lean}{Native/iPRA faithful translations and both round trips}.
The theorem names used in this paper are listed in the provenance section.

\bibitem{incoming}
ProveIt, \texttt{docs/incoming} at the pinned commit:
\texttt{ipra\_computation\_normal.zip},
\texttt{ipra\_counter\_evaluation\_2026-11-11.zip},
\texttt{ipra\_reduced\_clause\_calculus\_2026-11-11.zip},
\texttt{ipra\_rootfree\_clausal\_2026-11-11.zip}, and
\texttt{ipra\_uniform\_step.zip}.
\href{https://github.com/VladimirReshetnikov/ProveIt/tree/5d85023b0688e03b75f0ec3a04bb43ef0bb51705/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/docs/incoming}{Pinned incoming archive directory}.
The reported complete-program metrics and source hashes are preserved in
\texttt{evidence/incoming\_metrics.json}.

\bibitem{computationnormal}
ProveIt, \emph{Computation-normal iPRA and a smaller validated checker},
the first archive in reference~\cite{incoming}.
Its fresh-zero argument is a related use of aliases; the present principal
calculus does not use computation normalization.
\end{thebibliography}
'''


def main():
    parts = [HEADER]
    for name in ('introduction', 'theory', 'implementation', 'further'):
        parts.append((ROOT / 'paper' / (name + '.tex')).read_text())
    parts.append(BIBLIOGRAPHY)
    parts = [re.sub(r'\\texttt\{([^{}]{35,})\}',
                    lambda m: r'\path{' + m.group(1).replace(r'\_', '_') + '}',
                    part) for part in parts]
    parts.append(r'''
\clearpage
\appendix
\section{The complete trusted checker}
The listing below is the entire standalone acceptance program. The
proof producer, translations, and test utilities are not part of its
trusted code. This is the readable source; measurements in the paper
apply the stated normalization to the whole module.
\begin{lstlisting}
''')
    parts.append((ROOT / 'code/raw_parameter.py').read_text())
    parts.append('\n\\end{lstlisting}\n\\end{document}\n')
    (ROOT / 'ipra_parameter_substitution.tex').write_text('\n'.join(parts))


if __name__ == '__main__':
    main()
