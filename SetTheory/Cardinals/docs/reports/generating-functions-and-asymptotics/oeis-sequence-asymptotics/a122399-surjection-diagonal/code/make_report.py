#!/usr/bin/env python3
"""Deterministically assemble the audited Markdown source as publication-style TeX."""
from pathlib import Path
import subprocess, re
P=Path(__file__).parent
s=(P/'proof.md').read_text()
s=s[s.index('## Status and attribution'):]
s=s.replace('## Status and attribution','## Results and attribution')
# Nonmathematical production details belong in the reproducibility README.
a=s.index('Current targeted searches');b=s.index('\n## 1.',a)
s=s[:a]+s[b:]
s=s.replace('The working decimal output before the exact-rational contamination check was superseded; only the present generated files and displayed constants are authoritative. Independent mathematical audit remains required before treating the manuscript as publication-ready.','An independent audit and clean replay accompany this report. Conventional peer review remains appropriate before publication.')
s=s.replace(r''' b_{m,n}=\frac1{2\pi i}\int_{c-i\infty}^{c+i\infty}
 \frac{p(z)}{X(z)^{m+1}z^{n+1}}\,dz
 =\frac{n+1}{m}\frac1{2\pi i}\int_{c-i\infty}^{c+i\infty}
 X(z)^{-m}z^{-n-2}\,dz.\tag{2.1}''',r'''\begin{aligned}
 b_{m,n}&=\frac1{2\pi i}\int_{c-i\infty}^{c+i\infty}
 \frac{p(z)}{X(z)^{m+1}z^{n+1}}\,dz\\
 &=\frac{n+1}{m}\frac1{2\pi i}\int_{c-i\infty}^{c+i\infty}
 X(z)^{-m}z^{-n-2}\,dz.
\end{aligned}\tag{2.1}''')
start=s.index(' a_n=\\frac{C D^n(n!)^2}');end=s.index('\\tag{4.1}',start)
s=s[:start]+r'''\begin{aligned}
 a_n=\frac{C D^n(n!)^2}{\sqrt n}\Bigg[1
 &-\frac{0.0600744155748035800316371200380}{n}\\
 &+\frac{0.00759452281787645507680871266458}{n^2}\\
 &+\frac{0.00371322633571244961947936026057}{n^3}\\
 &-\frac{0.000362980958541489832391365216986}{n^4}
 +O(n^{-5})\Bigg].
\end{aligned}'''+s[end:]
s=s.replace(r'\mathbb EK_n=\mu n+\mu_0+O(n^{-1}),\qquad',r'\begin{aligned}\mathbb EK_n&=\mu n+\mu_0+O(n^{-1}),\\')
s=s.replace(r'\operatorname{Var}(K_n)=\sigma^2 n+O(1),',r'\operatorname{Var}(K_n)&=\sigma^2 n+O(1),\end{aligned}')
s=s.replace(r' \mu=0.873702433239668330496568304721,\quad',r'\begin{aligned} \mu&=0.873702433239668330496568304721,\\')
s=s.replace(r' \sigma^2=0.0889169868271170325484054553784,\quad',r' \sigma^2&=0.0889169868271170325484054553784,\\')
s=s.replace(r' \mu_0=0.144565688577761026837729354227.',r' \mu_0&=0.144565688577761026837729354227.\end{aligned}')
questions=r'''
## 8. Questions left by this analysis

The results separate three different levels of control: an exact contour with an explicit exponential tail, a fixed-order algebraic saddle expansion, and an asymptotic inverse. Several natural extensions require additional arguments.

1. **Exponentially improved expansions.** Locate and classify the complex saddles of \(z\Log(1+e^{-z})\), determine which are reached by valid contour deformations, and obtain an optimally truncated expansion with a controlled secondary-saddle remainder. The exact strip decomposition alone does not answer this question.
2. **Directions approaching the boundary.** Determine uniform laws when \(m/n\to0\) or \(m/n\to\infty\), including the transition scales where the compact-direction expansion ceases to be uniform. These regimes may require different saddle coordinates and block-count normalizations.
3. **Effective finite-input inverse bounds.** Turn the implicit all-orders constants into computable numerical bounds and starting thresholds, combining analytic Taylor estimates with the explicit contour tail. This would make the ceiling envelope a certified finite-input bracket and could reduce the need for exact comparisons away from sequence-value boundaries.
4. **Sharper block-count laws.** Prove a local limit theorem, explicit Edgeworth terms, or a uniform large-deviation estimate for the block count. The analytic marking germ provides the central cumulants, but the required global Fourier or tilted-contour estimates are not supplied here.

These are limitations and possible continuations of this analysis, not claims that the corresponding general techniques or all related results are absent from the literature.
'''
s=s.replace('\n## Sources and reproducibility',questions+'\n## Sources and reproducibility')
body=subprocess.run(['pandoc','--from=markdown+tex_math_single_backslash+raw_tex','--to=latex','--wrap=none'],input=s,text=True,check=True,capture_output=True).stdout
body=re.sub(r'\\texttt\{([^{}]*)\}', lambda m:r'\nolinkurl{'+m.group(1).replace(r'\_', '_')+'}', body)
body=re.sub(r'https?://[^\s)]+', lambda m:r'\url{'+m.group(0)+'}', body)
preamble=r'''\documentclass[11pt,letterpaper]{article}
\pdfinfoomitdate=1
\pdftrailerid{}
\pdfsuppressptexinfo=15
\usepackage[margin=1in]{geometry}
\usepackage{amsmath,amssymb,amsthm}
\usepackage[T1]{fontenc}
\pdfmapfile{+lm.map}
\pdfmapfile{+cm.map}
\pdfmapfile{+symbols.map}
\usepackage{lmodern,microtype}
\usepackage[hidelinks]{hyperref}
\usepackage{xurl,enumitem}
\setlist{itemsep=3pt,topsep=5pt}
\setcounter{secnumdepth}{0}
\providecommand{\tightlist}{\setlength{\itemsep}{0pt}\setlength{\parskip}{0pt}}
\newcommand{\Log}{\operatorname{Log}}
\allowdisplaybreaks[2]
\hypersetup{pdftitle={Asymptotic enumeration and inversion for A122399},pdfsubject={Exact contours, all orders asymptotics, inversion, block fluctuations, and congruences}}
\title{Asymptotic enumeration and inversion for A122399}
\author{A proof and reproducible research report}
\date{1 October 2026}
\begin{document}
\maketitle
\begin{abstract}
For $a_n=\sum_k k^n k!S(n,k)$, we prove the leading equivalent already recorded in OEIS and obtain a complete fixed-order expansion with explicit coefficients. An exact vertical contour gives a branch-safe representation and a simple, nonasymptotic exponential truncation bound. The same method yields compact-direction two-size asymptotics, Gaussian block-count fluctuations, and a controlled inverse with integer-threshold envelopes. An elementary appendix proves the posted mod-prime periodicity conjecture, in the sense that $p-1$ is a period, and extends it to prime powers. The standard saddle methodology and existing leading result are explicitly credited.
\end{abstract}
'''
(P/'a122399-report.tex').write_text(preamble+body+'\n\\end{document}\n')
print('Wrote a122399-report.tex')
