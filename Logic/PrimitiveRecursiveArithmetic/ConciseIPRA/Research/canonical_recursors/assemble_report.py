#!/usr/bin/env python3
"""Assemble one standalone LaTeX report; optionally compile its PDF."""
from pathlib import Path
import argparse
import json
import subprocess

ROOT = Path(__file__).resolve().parent


def read(name):
    return (ROOT / name).read_text()


def table(rows, caption):
    lines = [r'\begin{center}', r'\small',
             r'\begin{tabular}{lrrrr}', r'\toprule',
             r'Complete module & Tokens & AST & Bytes & Gzip 9\\', r'\midrule']
    lines += ['{} & {} & {} & {} & {}\\\\'.format(*row) for row in rows]
    lines += [r'\bottomrule', r'\end{tabular}', r'\par\smallskip', caption,
              r'\end{center}']
    return '\n'.join(lines) + '\n'


def flatten(text):
    import re
    return re.sub(r'\\input\{([^}]+)\}', lambda m: flatten(read(m[1])), text)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--compile', action='store_true')
    args = parser.parse_args()
    strict = json.loads(read('strict/results.json'))['modes']
    rows = []
    for mode, name in [('scalar', 'Scalar $I$, seven rules'),
                       ('raw', 'Raw $R$, seven rules'),
                       ('canonical', 'Canonical $R$, six rules')]:
        m = strict[mode]['metrics']
        rows.append((name, m['significant_tokens'], m['ast_nodes_without_docstrings'],
                     m['normalized_bytes_without_docstrings'], m['normalized_gzip9_bytes']))
    (ROOT / 'evidence/strict_metrics_table.tex').write_text(
        table(rows, 'Matching strict implementations; normalization and both interfaces are charged.'))
    compact = {m['file']: m for m in json.loads(read('compact/evidence/metrics.json'))['modules']}
    rows = []
    for key, name in [('reference/checker_bytes.py', 'Frozen compact byte control'),
                       ('code/checker_compact_zero.py', 'Refined compact byte profile'),
                       ('reference/checker_ast.py', 'Frozen compact AST control'),
                       ('code/checker_ast_zero.py', 'Refined compact AST profile'),
                       ('code/checker_strict_control.py', 'Matched strict guarded control'),
                       ('code/checker_strict.py', 'Refined strict guarded checker')]:
        m = compact[key]
        rows.append((name, m['significant_tokens'], m['ast_nodes'],
                     m['normalized_bytes'], m['gzip9_normalized_bytes']))
    (ROOT / 'evidence/compact_metrics_table.tex').write_text(
        table(rows, 'Existing scalar calculus only. Byte and AST improvements use different modules.'))

    core = read('theory/canonical_R.tex')
    core = core[core.index(r'\section{Scope and the exact mathematical change}'):
                core.index(r'\appendix')]
    core = core.replace(
        'Accordingly this note establishes a mathematical change of presentation and a smaller explicit rule inventory. It establishes neither an absolute minimum nor a smaller complete Python checker.',
        'Accordingly this theorem establishes a mathematical change of presentation and a smaller explicit rule inventory. The separately measured matching strict implementation is also smaller; no absolute or compact-checker minimum for this new calculus follows.')
    preamble = r'''\documentclass[11pt]{article}
\usepackage[T1]{fontenc}
\usepackage{lmodern,amsmath,amssymb,amsthm,mathtools,mathrsfs,enumitem,booktabs}
\usepackage[margin=1in,headheight=15pt]{geometry}
\usepackage{microtype,xcolor,fancyhdr,listings}
\usepackage[colorlinks=true,linkcolor=teal!65!black,urlcolor=teal!65!black,citecolor=teal!65!black]{hyperref}
\hypersetup{pdftitle={iPRA with one explicit computation schema},
 pdfauthor={Prepared for Vladimir Reshetnikov},
 pdfsubject={Canonical successor-seeded syntax, bi-interpretability, and complete-checker accounting},
 pdfkeywords={iPRA, intuitionistic arithmetic, primitive recursion, axiomatization}}
\newtheorem{theorem}{Theorem}[section]
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{proposition}[theorem]{Proposition}
\newtheorem{corollary}[theorem]{Corollary}
\theoremstyle{definition}
\newtheorem{definition}[theorem]{Definition}
\newtheorem{remark}[theorem]{Remark}
\newcommand{\norm}[1]{\nu(#1)}
\newcommand{\subc}[2]{#1\langle #2\rangle}
\newcommand{\lit}{\mathrel{\equiv}}
\newcommand{\Rfree}{\mathcal R_{\mathrm{free}}}
\newcommand{\Cnorm}{\mathcal C_\nu}
\newcommand{\Knorm}{\mathcal K_\nu}
\newcommand{\ipra}{\mathsf{iPRA}}
\newcommand{\llbracket}{\mathopen{[\![}}
\newcommand{\rrbracket}{\mathclose{]\!]}}
\newcommand{\file}[1]{{\small\nolinkurl{#1}}}
\setcounter{tocdepth}{1}
\setlength{\emergencystretch}{2em}
\pagestyle{fancy}
\fancyhf{}
\fancyhead[L]{\small iPRA: canonical recursors}
\fancyhead[R]{\small November 2026}
\fancyfoot[C]{\thepage}
\lstset{basicstyle=\ttfamily\footnotesize,breaklines=true,columns=fullflexible,
 keepspaces=true,showstringspaces=false,frame=single,rulecolor=\color{gray!45}}
\title{\textbf{iPRA with one explicit computation schema}\\[0.4em]
\large Canonical successor-seeded syntax and complete-checker accounting}
\author{Prepared for Vladimir Reshetnikov}
\date{12 November 2026}
\begin{document}
\maketitle
\begin{abstract}
We give a presentation of intuitionistic primitive recursive arithmetic with
six inference patterns, two numerical constructors in addition to variables,
and one explicit computation schema. Successor is defined by a
successor-seeded recursor. Its zero computation is imposed as a canonical
spelling of terms, and normalized substitution is specified and charged.
We prove both translations to the existing arithmetic and both composites,
including the recursor body-extensionality lemma required by normalization.
A complete strict checker has 4,611 normalized bytes against 4,923 for a
matching seven-rule scalar control, a 6.34 percent reduction. A separate
516-byte refinement improves the existing compact guarded calculus and is
not assigned to the new axiomatization. We also prove two boundaries: a
scalar self-seeded language cannot define predecessor, and induction on
zero equations does not recover arbitrary equation induction, even with
coverage and successor injectivity. The latter uses a nonstandard
two-point-fiber countermodel. All new metatheorems are written proofs;
the archive includes executable tests, exact source controls, and
reproduction instructions, without claiming new proof-assistant verification
or an absolute minimum.
\end{abstract}
\clearpage
\tableofcontents
\newpage
'''
    pieces = [preamble, read('theory/assessment.tex'), core,
              read('theory/implementation.tex'), read('theory/obstruction.tex'),
              read('theory/zero_induction_countermodel.tex'),
              read('theory/further_research.tex'), r'\clearpage\appendix',
              r'''\section*{Attribution for the inherited appendices}
The next seven source sections are reproduced from the pinned ProveIt
snapshot under its MIT No Attribution license. They are reference material,
not new contributions of this report. Their original notations and internal
attribution are retained. The two successor-seeded sections justify the raw
$R$ arithmetic used above. The remaining sections give the complete scalar
logic and arithmetic bridge. Their separate files are also in the archive.
The local files \file{successor_seed_prelogic.tex} and
\file{successor_seed_bootstrap.tex} are exact copies of
\file{Research/successor_seed_completion/theory/prelogic.tex} and
\file{Research/successor_seed_completion/theory/bootstrap.tex}, respectively.
''', read('theory/successor_seed_prelogic.tex'),
              read('theory/successor_seed_bootstrap.tex'),
              read('reference/inherited_choice_basis.tex'),
              read('reference/inherited_ordinary_bridge.tex'),
              read('reference/scalar_predecessor.tex'),
              read('reference/equality_reflection.tex'),
              read('reference/primitive_recursion.tex'),
              r'\clearpage\section{The complete strict canonical checker}',
              'The following normalized module is independently executable. Its full cost appears in Section~\\ref{sec:implementation}.\n',
              r'\begin{lstlisting}[language=Python]',
              read('strict/canonical_checker.normalized.py'), r'\end{lstlisting}',
              r'\section{The separate compact scalar byte profile}',
              'This implements the existing guarded calculus, with its documented public-input contract. It is not the canonical-$R$ program.\n',
              r'\begin{lstlisting}[language=Python]',
              read('compact/code/checker_compact_zero.py'), r'\end{lstlisting}',
              r'''\clearpage
\begin{thebibliography}{9}
\bibitem{repo} Vladimir Reshetnikov and ProveIt contributors.
\emph{Concise presentations of intuitionistic primitive recursive arithmetic}.
Snapshot \texttt{8eb71c1e570e07ef45ead686628e77f18ef34798}.
\href{https://github.com/VladimirReshetnikov/ProveIt/tree/8eb71c1e570e07ef45ead686628e77f18ef34798/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA}{Pinned repository collection}.
\bibitem{shared} ProveIt contributors. Successor-seeded and shared-continuation research lineage,
\file{Research/successor_seed_completion/theory/prelogic.tex}
and \file{Research/successor_seed_completion/theory/bootstrap.tex}, in the snapshot above.
\bibitem{erasure} ProveIt contributors. Scalar predecessor bootstrap,
\file{Research/certified_zero/reference/scalar_predecessor.tex},
with its inherited attribution, in the snapshot above.
\bibitem{forward} ProveIt contributors. Equality reflection and quantifier-free induction,
\file{Research/certified_zero/reference/equality_reflection.tex},
with its inherited attribution, in the snapshot above.
\bibitem{progress} ProveIt contributors. Primitive-recursion compiler,
\file{Research/certified_zero/reference/primitive_recursion.tex},
with its inherited progress-closure attribution, in the snapshot above.
\bibitem{finite} ProveIt contributors. Finite-control and relational obstructions,
\file{Research/local_scopes/theory/finite_profiles.tex} and
\file{relational_obstruction.tex}, in the snapshot above.
\bibitem{kernel} ProveIt contributors. Native kernel comparisons,
\file{Lean/ConciseIPRA/NativeMinimal.lean} and
\file{NativeReversal.lean}, and the ordinary scalar bridge,
\file{NativeBiInterpretation.lean}, in the snapshot above.
\end{thebibliography}
\end{document}
''']
    report = flatten('\n\n'.join(pieces))
    (ROOT / 'report.tex').write_text(report)
    print(json.dumps({'report_tex_bytes': len(report.encode()), 'standalone': r'\input{' not in report}))
    if args.compile:
        for _ in range(3):
            run = subprocess.run(['pdflatex', '-interaction=nonstopmode',
                                  '-halt-on-error', 'report.tex'], cwd=ROOT,
                                 capture_output=True, text=True)
            if run.returncode:
                print(run.stdout[-10000:])
                raise SystemExit(run.returncode)
        print('Compiled report.pdf')


if __name__ == '__main__':
    main()
