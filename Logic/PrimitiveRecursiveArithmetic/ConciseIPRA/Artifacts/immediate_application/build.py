"""Build the standalone LaTeX report and its PDF using installed TeX tools."""
from pathlib import Path
import shutil
import subprocess
import importlib.util

ROOT = Path(__file__).resolve().parent


def text(name):
    return (ROOT / name).read_text()


def main():
    preamble = text("reference/article_preamble.tex")
    preamble += r"""
\usepackage{listings}
\usepackage{microtype}
\usepackage{xurl}
\ifdefined\pdfmapfile
\pdfmapfile{}
\pdfmapfile{+lm.map}
\pdfmapfile{+cm.map}
\pdfmapfile{+symbols.map}
\pdfmapfile{+rsfs.map}
\fi
\definecolor{codeback}{RGB}{246,248,250}
\lstset{basicstyle=\ttfamily\small,breaklines=true,breakatwhitespace=false,
  columns=fullflexible,keepspaces=true,showstringspaces=false,
  backgroundcolor=\color{codeback},frame=single,rulecolor=\color{gray!30},
  xleftmargin=.4em,xrightmargin=.4em,aboveskip=1em,belowskip=1em}
\setlength{\emergencystretch}{3em}
\renewcommand{\rulename}[1]{\textnormal{\textsc{#1}}}
\renewcommand{\Lean}[1]{{\small\texttt{#1}}}
\hypersetup{pdftitle={A smaller checked presentation of iPRA},
 pdfauthor={Research report prepared for Vladimir Reshetnikov},
 pdfsubject={479-byte compact and 637-byte validated proof checkers; scope and limits}}
\begin{document}
\begin{titlepage}
\centering
\vspace*{1.7cm}
{\Large Intuitionistic primitive recursive arithmetic\par}
\vspace{.8cm}
{\Huge\bfseries A smaller checked presentation\par}
\vspace{.7cm}
{\LARGE Immediate substitution, exact acceptance,\par
and the limits of the reduction\par}
\vspace{1.5cm}
{\large Prepared for Vladimir Reshetnikov\par}
\vspace{.3cm}
{\large November 12, 2026\par}
\vspace{1.4cm}
\begin{minipage}{.86\textwidth}
\textbf{Established:} a compact checker decreases from 487 to 479
normalized bytes, and a fully validating companion from 646 to 637.
Both preserve the exact finite acceptance relation of their matched
references. The full theory, its interpretations, proof arguments,
source files, and reproduction evidence are included.

\medskip
\textbf{Still open:} a new axiomatization below all current complexity
coordinates. No arithmetic or logical axiom is deleted, and the independent
248-token and 270-AST-node records remain unbeaten.
\end{minipage}
\vfill
{\small Repository snapshot: \texttt{36d37fc1071fe289371f6bcd7dcfa0eac593a5a6}\par}
\end{titlepage}
\pagenumbering{roman}
\tableofcontents
\clearpage
\pagenumbering{arabic}
"""
    parts = [preamble, text("sections/results.tex"),
             "\\chapter{Axioms and both interpretations}\n\\label{ch:theory}\n",
             text("sections/interpretations.tex"), text("sections/protocol.tex"),
             "\\chapter{Proof of the implementation reduction}\n\\label{ch:proof}\n",
             text("sections/implementation_proof.tex"),
             text("sections/obstructions.tex"), text("sections/alias_obstruction.tex"),
             text("sections/reproduction.tex"),
             "\\appendix\n"]
    foundation = text("reference/ch01_base.tex")
    foundation = foundation.replace(r"\cref{claus:sec:five}",
                                    "the clause-calculus chapter of the source article")

    foundation = foundation.replace(r"\label{base:cor:rot}", r"\label{base:cor:rot}\leavevmode\par")
    foundation = foundation.replace(r"\label{base:thm:primrec}", r"\label{base:thm:primrec}\leavevmode\par")
    foundation = foundation.replace(r"""\[
 H(3u)=\sel\bigl(N(3u),G(3u),3u\bigr)
      =\sel\bigl(N(u),\ 3G(u)+N(u),\ 3u\bigr)=3\,\sel\bigl(N(u),G(u),u\bigr)
      =3H(u).
\]""", r"""\begin{align*}
 H(3u)&=\sel\bigl(N(3u),G(3u),3u\bigr)\\
      &=\sel\bigl(N(u),\ 3G(u)+N(u),\ 3u\bigr)\\
      &=3\,\sel\bigl(N(u),G(u),u\bigr)=3H(u).
\end{align*}""")
    foundation = foundation.replace(r"""  =N\bigl(3\,\It{y}{2^{x}}{u}{H(u)}\bigr)
  =N\bigl(\It{y}{2^{x}}{u}{H(u)}\bigr)=L(x,y),""", r"""  =N\bigl(3\,\It{y}{2^{x}}{u}{H(u)}\bigr)\\
  &=N\bigl(\It{y}{2^{x}}{u}{H(u)}\bigr)=L(x,y),""")
    marker = r"\label{base:chap}"
    foundation = foundation.replace(marker, marker + r"""

\begin{quote}\small
\textbf{Attribution and editorial note.} This appendix reproduces the
foundational chapter of the pinned ProveIt article, under its MIT No
Attribution license. It is inherited mathematics, not a new result of this
package. Typographic reflow changes no mathematical content. Chapter
numbering is local to this report; one cross-reference to
the omitted clause chapter is rendered as a textual reference. The exact
original source is retained in \path{reference/ch01_base.tex}.
\end{quote}
""", 1)
    parts.append(foundation)
    parts.append("\\chapter{Complete measured acceptance modules}\n")
    for name, title in [("code/checker479.py", "Compact guarded interface: 479 bytes"),
                        ("code/checker637.py", "Validated native interface: 637 bytes")]:
        parts += ["\\section{" + title + "}\n", "\\begin{lstlisting}[language=Python]\n",
                  text(name), "\\end{lstlisting}\n"]
    parts.append("\\end{document}\n")
    source = ROOT / "ipra_immediate_application.tex"
    source.write_text("\n".join(parts))
    build = ROOT / "build"
    build.mkdir(exist_ok=True)
    helper_spec = importlib.util.spec_from_file_location("private_tex_builder", ROOT / "tools/build_pdf.py")
    helper = importlib.util.module_from_spec(helper_spec)
    helper_spec.loader.exec_module(helper)
    helper.build(source, ROOT / "ipra_immediate_application.pdf", ROOT / "evidence/pdf_build.log")
    print("Built ipra_immediate_application.tex and ipra_immediate_application.pdf")


if __name__ == "__main__":
    main()
