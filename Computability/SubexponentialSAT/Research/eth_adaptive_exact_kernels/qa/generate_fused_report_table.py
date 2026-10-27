from pathlib import Path
import json
R=Path(__file__).resolve().parents[1]
d=json.loads((R/'results/fused_cauchy_benchmark_mask_all.json').read_text())
lines=[r'''\subsection{Fused recurrence against the matched quadratic baseline}
The final comparison uses the shared power-of-two \texttt{MaskRing} backend
in both algorithms, matching the late implementation's reduction optimization.
Both include complete fresh setup, both dense tables, known triangular zeros,
and one unit inversion. The baseline is an independently authored mathematical
reproduction, not the archive executable. Every timed output was checked outside
the clock. Five paired alternating-order samples and symmetric warmups were used.

The final record concatenates disjoint small and large fixture runs without
changing their raw samples; their source-file hashes are included in the JSON.
Table~\ref{tab:fused-times} shows all 23 records. Precision is $p=4N+16$,
$\zeta=U$, and times are wall-clock medians in milliseconds. The multiplication
ratio includes preparation, not just table loops.
\begingroup\small
\begin{longtable}{@{}rrrrrrrr@{}}
\caption{Matched one-inversion quadratic baseline versus fused transitions.}\label{tab:fused-times}\\
\toprule
$N$&$i$&$p$&Baseline&Fused&Wall ratio&CPU ratio&Mult. ratio\\\midrule\endfirsthead
\toprule
$N$&$i$&$p$&Baseline&Fused&Wall ratio&CPU ratio&Mult. ratio\\\midrule\endhead''']
for x in d['records']:
 ratio=x['baseline_counts']['total_multiplications']/x['fused_counts']['total_multiplications']
 lines.append(f"{x['N']} & {x['i']} & {x['precision']} & {1000*x['baseline_median_seconds']:.3f} & {1000*x['fused_median_seconds']:.3f} & {x['wall_speedup']:.2f} & {x['cpu_speedup']:.2f} & {ratio:.2f} "+r'\\')
lines.append(r'''\bottomrule\end{longtable}\endgroup
At $N=256$, $p=1040$, the three grid choices give baseline/fused wall-time
ratios $1.72$, $2.29$, and $1.46$, with CPU ratios $1.72$, $2.30$, and $1.43$.
The corresponding total multiplication ratios are about $2.34$--$2.42$.
They are different quantities: the baseline's scalar multiplications can be
cheaper than the fused algorithm's general ring multiplications.

Across all 23 final records the wall ratio ranges from about $.44$ to $3.05$;
values below one are retained regressions. The original percent-reduction
backend experiments and a confirmatory run are also preserved, including
additional regressions. They are not pooled with the mask-matched run because
the backend differs. The final backend was chosen to match an optimization
already present in the late code, not to imply that every earlier run improved.
Shared-host noise, precision, grid choice, and preprocessing prevent a universal
runtime claim. These are full-table component experiments, not SAT timings or
partial/on-demand feature benchmarks.''')
(R/'fused_table.tex').write_text('\n'.join(lines)+'\n')
