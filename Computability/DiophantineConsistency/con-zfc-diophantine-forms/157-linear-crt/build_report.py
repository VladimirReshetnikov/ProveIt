#!/usr/bin/env python3
"""Build a standalone LaTeX report and compile its PDF."""
from pathlib import Path
from collections import Counter
import argparse,json,re,shutil,subprocess,tempfile
ROOT=Path(__file__).resolve().parent

PREAMBLE=r"""\documentclass[11pt]{article}
\usepackage[T1]{fontenc}
\usepackage[utf8]{inputenc}
\usepackage{lmodern,microtype}
\usepackage[margin=0.82in]{geometry}
\usepackage{amsmath,amssymb,amsthm,mathtools}
\usepackage{booktabs,array,longtable}
\usepackage{xcolor,fancyhdr,enumitem,xurl}
\usepackage[colorlinks=true,linkcolor=blue!42!black,citecolor=blue!42!black,urlcolor=blue!42!black]{hyperref}
\definecolor{ink}{RGB}{25,43,64}
\setlength{\parindent}{0pt}
\setlength{\parskip}{0.4em}
\setlength{\headheight}{14pt}
\emergencystretch=2em
\allowdisplaybreaks
\setlist{nosep,leftmargin=*}
\pagestyle{fancy}
\fancyhf{}
\fancyhead[L]{\small Linear CRT radii and semantic radix recovery}
\fancyhead[R]{\small ProveIt research}
\fancyfoot[C]{\thepage}
\newtheorem{theorem}{Theorem}[section]
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{proposition}[theorem]{Proposition}
\newcommand{\Con}{\operatorname{Con}}
\hypersetup{pdftitle={Linear CRT radii and semantic radix recovery},
pdfauthor={AI-assisted research prepared for Vladimir Reshetnikov and ProveIt},
pdfsubject={Explicit quartic Diophantine equations equivalent to syntactic ZFC inconsistency}}
\title{\color{ink}\bfseries Linear CRT radii\\and semantic radix recovery\\[0.5em]
\large An explicit quartic for syntactic ZFC consistency}
\author{AI-assisted mathematical research\\[0.3em]
\normalsize Prepared for Vladimir Reshetnikov and the ProveIt project}
\date{25 October 2026}
\begin{document}
\maketitle
\thispagestyle{empty}
\begin{abstract}
We give a completely specified quartic in 238 unrestricted integer variables
whose unsolvability is provably equivalent in ZFC to syntactic consistency
of ZFC, using the identified inherited numerical-calculus calibration.
The equation is the sum of squares of 174 printed quadratic residuals;
its collected expansion has 13,149 monomials and coefficient height 6,144.
Two 239-variable companions trade support against height.

The arithmetic reduction uses a single growth value \(F=t^t\) for both
proof-label separation and a binomial CRT radius. An even index chart and
an affine majorant that cannot be a unit recover the radix without a private
square witness. An existing power request then recovers the sign of the beta
spacing, permitting its odd multiplier to be unsquared. Three arithmetic
coordinates disappear, and exact reversible row operations give the reported
polynomials. Complete coefficient files, constructive proofs, restoration
certificates, independent finite checkers, and deterministic rebuild code
accompany the article.

This is an explicit improvement in the inspected direct small-coefficient
quartic lineage. It is neither a proof of consistency, a global minimality
claim, nor a newly compiled end-to-end proof-assistant formalization.
\end{abstract}
\vfill
\begin{center}\small
Comparison snapshot:\\
\texttt{7a8da414376a80b90ecf799f37ceb26fb9ac674e}\\
All unknowns in the three new equations range over \(\mathbb Z\).
\end{center}
\newpage
\tableofcontents
\newpage
"""

def read_equation(profile):
    return json.loads((ROOT/'equations'/profile/'equation.json').read_text())

def term(c,monomial,first):
    sign=('-' if c<0 else '') if first else (' - ' if c<0 else ' + ')
    absolute=abs(c)
    coefficient=str(absolute) if absolute!=1 or not monomial else ''
    factors=[]
    for v,power in sorted(Counter(monomial).items()):
        factor='x_{'+str(v)+'}'
        if power!=1:factor+='^{'+str(power)+'}'
        factors.append(factor)
    return sign+coefficient+r'\,'.join(factors)

def row_tex(index,row):
    pieces=[term(c,m,i==0) for i,(c,m) in enumerate(row['terms'])]
    chunks=[''.join(pieces[i:i+5]) for i in range(0,len(pieces),5)]
    lines=[r'R_{'+str(index)+r'}={}&'+chunks[0]]
    lines += [r'&{}'+s for s in chunks[1:]]
    return r'\begin{equation*}\begin{aligned}'+'\n'+(' \\\\\n'.join(lines))+'\n'+r'\end{aligned}\end{equation*}'+'\n'

def appendix():
    eq=read_equation('P238')
    text=r"""
\appendix
\section{Complete principal polynomial}\label{app:residuals}
All coordinates \(x_0,\ldots,x_{237}\) are unrestricted integers.
The single equation is exactly
\[
             \sum_{i=0}^{173}R_i(x_0,\ldots,x_{237})^2=0.
\]
The following list is complete. Symbols in this list are final coordinates;
their interpretations in the arithmetic construction are obtained through
the supplied restoration certificates. There are no coefficient ports or
additional implicit unknowns.
\begingroup
\small
\setlength{\abovedisplayskip}{5pt}
\setlength{\belowdisplayskip}{5pt}
"""
    text+=''.join(row_tex(i,row) for i,row in enumerate(eq['residuals']))
    text+=r"""
\endgroup
\section{Companion specifications and archive layout}
The other two equations are defined completely by their ordered variable
and residual lists:
\[
P_{239}^{\mathrm{sparse}}=\sum_{i=0}^{174}(S_i)^2,\qquad
P_{239}^{\mathrm{low}}=\sum_{i=0}^{174}(T_i)^2.
\]
Their respective directories are
\nolinkurl{equations/P239_sparse/} and
\nolinkurl{equations/P239_low_height/}.
Each contains the entire ordinary polynomial as residuals and as collected
coefficients, its exact metrics, and an explicit restoration certificate.
The supplied evaluator distinguishes the profiles by these names.

\begin{center}\small
\begin{tabular}{p{0.30\linewidth}p{0.62\linewidth}}
\toprule
Path & Contents\\
\midrule
\nolinkurl{report/report.tex}, \nolinkurl{report/report.pdf}
& Standalone article and compiled PDF.\\
\nolinkurl{equations/}
& Three complete polynomial specifications, all expanded coefficients,
and exact final certificates.\\
\nolinkurl{source/}
& Changed raw source, Horn factoring, monic projection and translation
records, and the intermediate polynomial.\\
\nolinkurl{code/}
& Deterministic source producer, frozen endpoint replay, separately written
finite checkers, corruption controls, and arithmetic diagnostics.\\
\nolinkurl{proofs/}, \nolinkurl{review/}
& Unbounded proofs, independent mathematical reviews and actual verification
receipts with their precise scopes.\\
\nolinkurl{inherited/factorial_free/}
& Attributed immediate predecessor, including ordinary proof closure,
logical interfaces, source code, data, and original notices.\\
\nolinkurl{comparisons/}
& Literal predecessor polynomials used for the measured comparisons.\\
\nolinkurl{SOURCE_LEDGER.json}, \nolinkurl{MANIFEST.sha256.json}
& Repository and archive pins, dependency boundary, and file identities.\\
\bottomrule
\end{tabular}
\end{center}
\end{document}
"""
    return text

def document():
    return PREAMBLE+(ROOT/'report/body.tex').read_text()+'\n'+appendix()

def parse_printed_rows(text):
    found=[]
    for block in re.findall(r'\\begin\{aligned\}(.*?)\\end\{aligned\}',text,re.S):
        match=re.match(r'\s*R_\{(\d+)\}=\{\}&(.*)',block,re.S)
        if not match:continue
        index=int(match.group(1));body=match.group(2)
        body=body.replace('\\\\','').replace('&{}','').replace(r'\,','')
        body=re.sub(r'\s+','',body)
        terms=[]
        for item in re.findall(r'[+-]?[^+-]+',body):
            sign=-1 if item.startswith('-') else 1
            item=item.lstrip('+-')
            factors=list(re.finditer(r'x_\{(\d+)\}(?:\^\{(\d+)\})?',item))
            if factors:
                coefficient=item[:factors[0].start()]
                c=int(coefficient) if coefficient else 1
                remaining=item
                monomial=[]
                for factor in reversed(factors):remaining=remaining[:factor.start()]+remaining[factor.end():]
                if remaining!=coefficient:raise ValueError('Unexpected printed monomial')
                for factor in factors:
                    monomial += [int(factor.group(1))]*int(factor.group(2) or 1)
            else:c=int(item);monomial=[]
            terms.append([sign*c,monomial])
        found.append((index,terms))
    return found

def check_generated():
    expected=document();path=ROOT/'report/report.tex'
    if path.read_text()!=expected:raise ValueError('Generated standalone report differs from authoritative inputs')
    rows=read_equation('P238')['residuals']
    parsed=parse_printed_rows(expected)
    if parsed!=[(i,row['terms']) for i,row in enumerate(rows)]:
        raise ValueError('Actual printed polynomial differs from JSON')

def build(tex_only=False):
    target=ROOT/'report';target.mkdir(exist_ok=True)
    (target/'report.tex').write_text(document())
    check_generated()
    if tex_only:return
    with tempfile.TemporaryDirectory(prefix='conzfc_linear_pdf_') as temporary:
        temporary=Path(temporary)
        shutil.copy2(target/'report.tex',temporary/'report.tex')
        for _ in range(3):
            run=subprocess.run(['pdflatex','-interaction=nonstopmode','-halt-on-error','-no-shell-escape','report.tex'],
                               cwd=temporary,capture_output=True,text=True)
            if run.returncode:
                (target/'FAILED_BUILD.log').write_text(run.stdout+run.stderr)
                raise RuntimeError('LaTeX build failed; see report/FAILED_BUILD.log')
        log=(temporary/'report.log').read_text()
        (target/'BUILD.log').write_text(log)
        if 'Overfull' in log or re.search(r'undefined references|Citation .* undefined|Reference .* undefined',log):
            raise RuntimeError('LaTeX layout or reference defect; see report/BUILD.log')
        shutil.copy2(temporary/'report.pdf',target/'report.pdf')
    print('Built report/report.pdf; every printed principal residual parsed back exactly.')

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tex-only',action='store_true')
    parser.add_argument('--check',action='store_true')
    args=parser.parse_args()
    if args.check:check_generated();print('Printed specification verified.')
    else:build(args.tex_only)
