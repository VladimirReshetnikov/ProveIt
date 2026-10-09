#!/usr/bin/env python3
"""Generate the self-contained TeX article from its template and saved timings."""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parents[1]
r=json.loads((ROOT/'results/benchmark.json').read_text())
paired=r'''\begin{table}[htbp]
\centering\small
\begin{tabular}{rrrrrr}
\toprule
$L$ & Box points & Strata & Stratified (ms) & Exhaustive (ms) & Ratio\\
\midrule
'''
for x in r['paired']:
    paired+=f"{x['L']} & {x['candidate_potentials']:,} & {x['strata']} & {1000*x['stratified_median_seconds']:.2f} & {1000*x['exhaustive_median_seconds']:.2f} & {x['exhaustive_over_stratified']:.2f}\\\\\n"
paired+=r'''\bottomrule
\end{tabular}
\caption{Median times for the same radius-two shell-profile query on an abstract height family. Ratio is exhaustive divided by stratified time; values below one are slowdowns for stratification. These are not native knot-recognition timings.}
\label{tab:paired}
\end{table}'''
binary=r'''\begin{table}[htbp]
\centering\small
\begin{tabular}{rrrrr}
\toprule
Height exponent $b$ & Strata & Work ticks & Augmentations & Median (ms)\\
\midrule
'''
for x in r['binary']:
    binary+=f"{x['height_exponent']:,} & {x['strata']} & {x['work']:,} & {x['augmentations']} & {1000*x['median_seconds']:.2f}\\\\\n"
binary+=r'''\bottomrule
\end{tabular}
\caption{Binary-size stress with height $L=2^b$ and fixed excess budget two. The integer arithmetic cost grows, while the number of strata and instrumented combinatorial work remain unchanged on this family.}
\label{tab:binary}
\end{table}'''
s=(ROOT/'article/article.tex.in').read_text()
s=s.replace('@@PAIRED_TABLE@@',paired).replace('@@BINARY_TABLE@@',binary)
assert '@@' not in s
(ROOT/'article/article.tex').write_text(s)
print('Generated self-contained article/article.tex from recorded benchmark medians.')
