"""Assemble the standalone LaTeX source from audited local components."""
from pathlib import Path
import ast
import csv
import io
import json
import tokenize

ROOT = Path(__file__).resolve().parent
REF = '62396b06020f794fa6dc01b4025a6a5db9d4d28a'
BASE = f'https://github.com/VladimirReshetnikov/ProveIt/tree/{REF}/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA'
FILES = [
    ('Token control', 'controls/checker_tokens_256.py'),
    ('Inferred-major token profile', 'checker_tokens.py'),
    ('AST control', 'controls/checker_ast_278.py'),
    ('Inferred-major AST profile', 'checker_ast.py'),
    ('Byte control', 'controls/checker_bytes_506.py'),
    ('Truthy-result byte profile', 'checker_bytes.py'),
    ('Byte profile, ordinary decrement', 'checker_bytes_readable_decrement.py'),
    ('Native public-goal control', 'controls/checker_native_656.py'),
    ('Native public-goal profile', 'checker_native.py'),
]
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
        tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}


def measurements():
    result = []
    for label, filename in FILES:
        original = (ROOT / 'code' / filename).read_text()
        compile(original, filename, 'exec')
        tree = ast.parse(original)
        # The selected standalone modules have no docstrings, but implement
        # the corpus's documented normalization for future reproduction.
        for node in ast.walk(tree):
            if isinstance(node, (ast.Module, ast.FunctionDef,
                                 ast.AsyncFunctionDef, ast.ClassDef)):
                if node.body and isinstance(node.body[0], ast.Expr):
                    v = node.body[0].value
                    if isinstance(v, ast.Constant) and isinstance(v.value, str):
                        node.body.pop(0)
        normalized = ast.unparse(tree) + '\n'
        result.append({'label': label, 'file': 'code/' + filename,
                       'tokens': sum(t.type not in SKIP for t in tokenize.generate_tokens(io.StringIO(normalized).readline)),
                       'ast_nodes': len(list(ast.walk(ast.parse(normalized)))),
                       'normalized_bytes': len(normalized.encode('utf-8'))})
    return result


def main():
    rows = measurements()
    (ROOT / 'evidence' / 'metrics.json').write_text(json.dumps(rows, indent=2) + '\n')
    with (ROOT / 'evidence' / 'metrics.csv').open('w', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    table = ['\\begin{center}\\small', '\\begin{tabular}{lrrr}', '\\toprule',
             'Complete module & Tokens & AST nodes & Bytes\\\\', '\\midrule']
    for r in rows:
        table.append(f"{r['label']} & {r['tokens']} & {r['ast_nodes']} & {r['normalized_bytes']}\\\\")
    table.extend(['\\bottomrule', '\\end{tabular}', '\\end{center}'])
    appendices = '\n\n'.join((ROOT / 'reference' / name).read_text() for name in [
        'inherited_choice_basis.tex', 'inherited_ordinary_bridge.tex',
        'scalar_predecessor.tex', 'equality_reflection.tex',
        'primitive_recursion.tex', 'guarded_core.tex',
        'zero_source_admissibility.tex', 'deterministic_auxiliary_composition.tex',
        'inherited_arity_checker.tex'])
    listings = []
    for label, filename in FILES:
        if filename.startswith('controls/'):
            continue
        listings.extend(['\\Needspace{8\\baselineskip}', '\\subsection{' + label + '}', '\\begin{lstlisting}[language=Python]',
                         (ROOT / 'code' / filename).read_text().rstrip(), '\\end{lstlisting}'])
    bibliography = [r'\begin{thebibliography}{99}']
    entries = [
        ('upstream', 'ProveIt contributors. Concise presentations of intuitionistic primitive recursive arithmetic. Pinned snapshot, 12 November 2026.', ''),
        ('corpus', 'ProveIt contributors. Collected research packages and current formalization.', '/Research'),
        ('generated', 'ProveIt contributors. Inherited arity encoding and generated-assumption proof; reproduced in this report.', '/Research/checked_refinement/reference/foundations'),
        ('constructed', 'ProveIt contributors. Constructed-computation certificate interface.', '/Research/constructed_computation'),
        ('guarded', 'ProveIt contributors. Guarded core and deterministic introduction.', '/Research/guarded_core'),
        ('source', 'ProveIt contributors. Literal-zero-source admissibility and source dispatch.', '/Research/source_dispatch'),
        ('lean-zero', 'ProveIt contributors. Lean formalization and source-admissibility results, as recorded in the pinned README.', ''),
        ('erasure', 'ProveIt contributors. Inherited scalar predecessor bootstrap; exact attributed appendix reproduced in this report.', '/Research/checked_refinement/reference/foundations'),
        ('progress', 'ProveIt contributors. Inherited equality reflection, pairing, and primitive-recursion compilation appendices; reproduced in this report.', '/Research/checked_refinement/reference/foundations'),
        ('forward', 'ProveIt contributors. Inherited native arithmetic and proof-certificate foundations.', '/Research/checked_refinement/reference/foundations'),
        ('transient', 'ProveIt contributors. Transient-seed arithmetic development.', '/Research/transient_seed'),
    ]
    for key, title, suffix in entries:
        bibliography.append('\\bibitem{' + key + '}' + title + '\n\\href{' + BASE + suffix + '}{Pinned primary source}.')
    bibliography.append(r'\end{thebibliography}')
    body = (ROOT / 'main_body.tex').read_text()
    for key, value in {'@@METRICS_TABLE@@': '\n'.join(table),
                       '@@INHERITED_APPENDICES@@': appendices,
                       '@@CHECKER_LISTINGS@@': '\n'.join(listings),
                       '@@BIBLIOGRAPHY@@': '\n'.join(bibliography)}.items():
        body = body.replace(key, value)
    assert '@@' not in body
    preamble = r'''\documentclass[11pt,letterpaper]{article}
\usepackage[T1]{fontenc}
\usepackage[utf8]{inputenc}
\usepackage{lmodern,microtype}
\ifdefined\pdfmapfile
\pdfmapfile{+lm.map}
\pdfmapfile{+cm.map}
\pdfmapfile{+symbols.map}
\fi
\usepackage[margin=0.9in,headheight=15pt]{geometry}
\usepackage{amsmath,amssymb,amsthm,mathtools}
\usepackage{booktabs,array,longtable,enumitem}
\usepackage{xcolor,listings,fancyhdr,xurl,needspace}
\definecolor{inkblue}{RGB}{26,56,89}
\definecolor{muted}{RGB}{74,84,95}
\usepackage[hypertexnames=false,colorlinks=true,linkcolor=inkblue,citecolor=inkblue,urlcolor=inkblue]{hyperref}
\hypersetup{pdftitle={iPRA with inferred elimination premises},pdfauthor={OpenAI, prepared for Vladimir Reshetnikov},pdfsubject={Complete iPRA proof checkers, equivalence proofs and reproducible complexity comparisons}}
\newtheorem{theorem}{Theorem}[section]
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{proposition}[theorem]{Proposition}
\newtheorem{corollary}[theorem]{Corollary}
\theoremstyle{definition}
\newtheorem{definition}[theorem]{Definition}
\newtheorem{remark}[theorem]{Remark}
\newcommand{\D}{\mathsf D}
\newcommand{\Q}{\mathsf Q}
\newcommand{\A}{\mathcal A}
\newcommand{\G}{\mathcal G}
\newcommand{\U}{\mathcal U}
\newcommand{\ipra}{\mathrm{iPRA}}
\setlength{\parindent}{0pt}
\setlength{\parskip}{5pt plus 1pt}
\setlength{\emergencystretch}{2em}
\setlist{topsep=4pt,itemsep=2pt,parsep=1pt}
\lstset{basicstyle=\ttfamily\scriptsize,breaklines=true,breakatwhitespace=false,
 columns=fullflexible,keepspaces=true,showstringspaces=false,frame=single,
 rulecolor=\color{muted!30},backgroundcolor=\color{muted!3},
 xleftmargin=3pt,xrightmargin=3pt,aboveskip=7pt,belowskip=7pt}
\pagestyle{fancy}
\fancyhf{}
\fancyhead[L]{\small\color{muted}iPRA with inferred elimination premises}
\fancyhead[R]{\small\color{muted}12 November 2026}
\fancyfoot[C]{\thepage}
\renewcommand{\headrulewidth}{0.3pt}
\title{\color{inkblue}\textbf{iPRA with inferred elimination premises}\\[5pt]
\large Smaller proof checkers below the audited comparison envelope}
\author{Prepared for Vladimir Reshetnikov}
\date{12 November 2026}
\begin{document}
\maketitle
\thispagestyle{empty}
\begin{abstract}
We simplify a complete proof-certificate presentation of intuitionistic
primitive recursive arithmetic by reconstructing an elimination's major
formula from its target and substitution data. The major must still be
proved. The resulting programs reduce the identified compact comparison
envelope from 256 significant Python tokens, 278 AST nodes and 506 normalized
bytes to 253 tokens, 275 nodes and 503 bytes, with different programs attaining
the three coordinates. A separate complete native public-goal checker falls
from 656 to 643 bytes, also improving both other coordinates. We give universal
simulation arguments, executable certificate translations, frozen controls,
and the full inherited logical and arithmetic bi-interpretation. Both
numerical domains are whole, equality is actual, and both composites have
graph $x=y$. The mathematical axioms are inherited; the new results concern
certificate structure and trusted implementation size. No absolute minimum
or new axiom deletion is claimed.
\end{abstract}
\vfill
\begin{center}\small
Comparison snapshot: \texttt{62396b06020f794fa6dc01b4025a6a5db9d4d28a}\\
Standalone LaTeX source, compiled PDF, proof checkers, controls and validation artifacts.
\end{center}
\clearpage
\tableofcontents
\clearpage
'''
    (ROOT / 'report.tex').write_text(preamble + body + '\n\\end{document}\n')
    print('Assembled report.tex; measured', len(rows), 'standalone modules.')


if __name__ == '__main__':
    main()
