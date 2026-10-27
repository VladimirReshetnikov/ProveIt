from pathlib import Path
import json
R=Path(__file__).resolve().parents[1]
d=json.loads((R/'results/balancing_benchmark.json').read_text())
lines=[r'''The final run contains eight fixed-shape $10$-by-$12$ fixtures and three
larger sparse fixtures with $2Q$ vertices on each side and four unit edges per
row. The latter keep the number of labels below the vertex count on both sides.
Table~\ref{tab:packing-times} shows all eleven records. Times are wall-clock
medians in milliseconds; $C/S$ and $D/S$ compare the cubic and dense-delta
methods against sparse deltas.
\begin{table}[htbp]\centering\small
\begin{tabular}{@{}lrrrrrrr@{}}\toprule
Family & $Q$ & Density & Cubic & Dense & Sparse & $C/S$ & $D/S$\\\midrule''']
for x in d['records']:
 fam='Fixed' if x['family']=='fixed-shape' else 'Four per row'
 m=x['medians']
 lines.append(f"{fam} & {x['labels']} & {x['input_density']:.3f} & {1000*m['cubic']:.3f} & {1000*m['dense']:.3f} & {1000*m['sparse']:.3f} & {x['cubic_over_sparse']:.2f} & {x['dense_over_sparse']:.2f} "+r'\\')
lines.append(r'''\bottomrule\end{tabular}
\caption{Packing kernel wall-time medians in milliseconds, five samples per
method. Ratios below one are regressions, not omitted results.}\label{tab:packing-times}
\end{table}
For the four-per-row fixtures at $Q=8,16,24$, sparse deltas reduce wall time
by factors $8.54$, $39.77$, and $100.87$ relative to full candidate scoring;
relative to the stronger dense-delta reference the factors are $1.53$,
$2.47$, and $2.73$. CPU ratios are closely comparable. Deterministic sparse
score-term counts are $159$, $341$, and $577$, compared with dense-delta
counts $432$, $1792$, and $4272$. These counts isolate the support saving
without mistaking shared initialization for free work.''')
(R/'balancing_table.tex').write_text('\n'.join(lines)+'\n')
d=json.loads((R/'results/cauchy_benchmark_confirm.json').read_text())
lines=[r'''Table~\ref{tab:cauchy-times} gives all twenty confirmatory records. Precision
is $p=4N+16$ throughout. The two time columns are full-table wall-clock
medians in milliseconds; the two ratios use wall and process-CPU medians,
respectively.
\begin{longtable}{@{}rrrrrrrr@{}}
\caption{Complete Cauchy feature tables, including shared batch setup and output.}\label{tab:cauchy-times}\\
\toprule
$N$ & $i$ & $p$ & Product & Recurrent & Wall ratio & CPU ratio & Mult. ratio\\\midrule\endfirsthead
\toprule
$N$ & $i$ & $p$ & Product & Recurrent & Wall ratio & CPU ratio & Mult. ratio\\\midrule\endhead''']
for x in d['records']:
 lines.append(f"{x['N']} & {x['i']} & {x['precision']} & {1000*x['product_median_seconds']:.3f} & {1000*x['recurrent_median_seconds']:.3f} & {x['measured_speedup']:.2f} & {x['measured_cpu_speedup']:.2f} & {x['multiplication_ratio']:.2f} "+r'\\')
lines.append(r'\bottomrule\end{longtable}')
(R/'cauchy_table.tex').write_text('\n'.join(lines)+'\n')
