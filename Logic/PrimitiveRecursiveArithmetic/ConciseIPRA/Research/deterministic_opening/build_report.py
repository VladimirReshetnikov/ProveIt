"""Assemble a standalone LaTeX report; optionally compile its PDF."""
from pathlib import Path
import argparse
import subprocess

ROOT = Path(__file__).resolve().parent
STEM = 'ipra_deterministic_opening'

PREAMBLE = r'''\documentclass[11pt,letterpaper]{article}
\usepackage[T1]{fontenc}
\usepackage{lmodern}
\usepackage[margin=1in]{geometry}
\usepackage{amsmath,amssymb,amsthm,mathtools}
\usepackage{booktabs,array,longtable}
\usepackage{microtype}
\usepackage{xcolor}
\usepackage{xurl}
\usepackage{listings}
\usepackage{enumitem}
\usepackage{fancyhdr}
\usepackage{hyperref}
\definecolor{ink}{HTML}{18344C}
\definecolor{codegray}{HTML}{F4F6F8}
\hypersetup{colorlinks=true,linkcolor=ink,urlcolor=ink,citecolor=ink,
 pdftitle={Deterministic witness opening for iPRA},
 pdfauthor={Research prepared for Vladimir Reshetnikov},
 pdfsubject={A three-rule presentation, full bi-interpretation, and complete checker measurements}}
\newtheorem{theorem}{Theorem}[section]
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{proposition}[theorem]{Proposition}
\newtheorem{corollary}[theorem]{Corollary}
\theoremstyle{definition}
\newtheorem{definition}[theorem]{Definition}
\newtheorem{remark}[theorem]{Remark}
\setlist{itemsep=3pt,topsep=6pt}
\setlength{\parskip}{4pt}
\setlength{\headheight}{15pt}
\setlength{\emergencystretch}{2em}
\pagestyle{fancy}
\fancyhf{}
\fancyhead[L]{\small Deterministic witness opening for iPRA}
\fancyhead[R]{\small November 11, 2026}
\fancyfoot[C]{\thepage}
\renewcommand{\headrulewidth}{0.3pt}
\lstset{language=Python,basicstyle=\ttfamily\footnotesize,
 backgroundcolor=\color{codegray},frame=single,rulecolor=\color{black!15},
 breaklines=true,columns=fullflexible,keepspaces=true,showstringspaces=false,
 aboveskip=10pt,belowskip=10pt,xleftmargin=5pt,xrightmargin=5pt}
\begin{document}
\thispagestyle{empty}
\begin{center}
{\small\sffamily\color{ink} CONCISE iPRA / RESEARCH REPORT}\par
\vspace{1.2em}
{\LARGE\bfseries A smaller inference interface for\par
intuitionistic primitive recursive arithmetic}\par
\vspace{.7em}
{\large Deterministic witness opening and measured checker reductions}\par
\vspace{.8em}
{Prepared for Vladimir Reshetnikov}\par
{November 11, 2026}
\end{center}
\vspace{1em}
\begin{abstract}
An equality-bearing witness elimination can determine its replacement from
one fixed instance of the formula being opened.  Specializing the opened
clause at that value leaves the outer goal unchanged and removes an
explicit replacement term, an equality-proof premise, and an intermediate
formula from the certificate interface.  The resulting presentation has
three rule families and one fixed reflexivity clause.  A bootstrap through
restricted openings and a strong substitution theorem proves equality of
the entire canonical clause consequence relation with the preceding
presentation.  It therefore preserves full first-order iPRA
bi-interpretability, whole domains, actual equality, and both identity
composites.  Its matched complete checker decreases from 2,273 to 2,253
normalized Python bytes.  Independently, a proved continuation refactor of
the existing compact calculus decreases its complete byte profile from
516 to 508 bytes and its separate AST profile from 278 to 276 nodes.
The new mathematical presentation is not the one implemented by the
508-byte checker.  Global minimality and a single-program improvement in
every size coordinate are not claimed.
\end{abstract}
\tableofcontents
\clearpage
'''

BIBLIOGRAPHY = r'''
\begin{thebibliography}{9}
\bibitem{baseline} V. Reshetnikov, ProveIt, \emph{Concise presentations of
intuitionistic primitive recursive arithmetic}, README and research
inventory at commit \texttt{17898ea7e6a1300dfdcad71040d5daeed67916d4}.
\href{https://github.com/VladimirReshetnikov/ProveIt/tree/17898ea7e6a1300dfdcad71040d5daeed67916d4/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA}{Pinned project directory}.
\bibitem{wd} \emph{Witness discharge}, incoming research archive
\texttt{ipra\_witness\_discharge\_2026-11-11.zip}, in the same pinned
project, \path{docs/incoming}.  Git blob
\texttt{3e2c86ca3590588ea3be3ebf24dd379a3a660ff1}.
The immediate control and supporting mathematical sources are reproduced
in the accompanying archive with provenance.
\bibitem{fullnf} \emph{Full normalization}, research package in
\path{Research/full_normalization} of the pinned project.  Written
termination, confluence, coherence, and canonical/raw comparison.
\bibitem{native} ProveIt Lean development, \texttt{NativeClausal},
\texttt{NativeBiInterpretation}, and \texttt{BiInterpretation}, at the
same pinned commit.  Selected exact source files are included for
reference; this report does not claim a new build or new Lean theorem.
\bibitem{python} Python Software Foundation, \emph{Python 3.12 Language
Reference}, Section 6.16, Evaluation order.
\url{https://docs.python.org/3.12/reference/expressions.html#evaluation-order}.
\end{thebibliography}
'''


def strip_header_docstring(text):
    if text.startswith('"""'):
        end = text.index('"""', 3) + 3
        return text[end:].lstrip()
    return text


def assemble():
    names = ['overview', 'automatic_opening', 'normalization',
             'interpretations', 'implementation', 'compact', 'further']
    pieces = [PREAMBLE]
    for name in names:
        pieces.append((ROOT / 'sections' / (name + '.tex')).read_text())
    pieces += [BIBLIOGRAPHY, r'\appendix' + '\n',
               r'\section{Complete selected checker}\label{app:source}' + '\n',
               'This listing is the entire executable module apart from its '
               'informational header docstring. The separately supplied file '
               'contains that header. Comments are not counted by the source '
               'normalization metric.\n',
               '\\begin{lstlisting}\n',
               strip_header_docstring((ROOT / 'code/checker_open.py').read_text()),
               '\\end{lstlisting}\n',
               r'\section{The separate 508-byte compact profile}' + '\n',
               'The following module implements the inherited compact protocol '
               'under its documented guarded public-goal contract. It is not '
               'the selected checker of the new three-rule theory.\n',
               '\\begin{lstlisting}\n',
               (ROOT / 'compact/code/compact.py').read_text(),
               '\\end{lstlisting}\n',
               r'\end{document}' + '\n']
    output = ROOT / (STEM + '.tex')
    output.write_text('\n'.join(pieces))
    return output


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--pdf', action='store_true')
    args = parser.parse_args()
    source = assemble()
    print('Assembled', source.name)
    if args.pdf:
        build = ROOT / 'build'
        build.mkdir(exist_ok=True)
        for _ in range(3):
            result = subprocess.run(
                ['pdflatex', '-interaction=nonstopmode', '-halt-on-error',
                 '-output-directory=build', source.name],
                cwd=ROOT, text=True, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT)
            (build / 'pdflatex-output.txt').write_text(result.stdout)
            if result.returncode:
                print(result.stdout[-7000:])
                raise SystemExit(result.returncode)
        (ROOT / (STEM + '.pdf')).write_bytes((build / (STEM + '.pdf')).read_bytes())
        print('Compiled', STEM + '.pdf')

