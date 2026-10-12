from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent
b=json.loads((ROOT/'results/benchmark.json').read_text())
rows=[]
for x in b['summaries']:
    name=x['case'].replace('saturated_genus_',r'$g=').replace('closed_nonorientable_copies_',r'$m=')
    if name.startswith('$'):name+='$'
    else:name=name.replace('_',' ')
    rows.append(f"{name} & {x['compressed_median_ms']:.3f} & {x['expanded_median_ms']:.3f} & {x['median_paired_ratio']:.3f} & {x['median_AA_ratio']:.3f} \\\\")
table=r'''\begin{table}[ht]
\centering\small
\begin{tabular}{@{}lrrrr@{}}
\toprule
Case & Condensed (ms) & Expanded (ms) & Paired ratio & A/A\\
\midrule
'''+ '\n'.join(rows)+r'''
\bottomrule
\end{tabular}
\caption{Complete abstract $H_1$ kernels, including exact Smith replay and output. Nine measured rounds; medians and paired ratios. No source cut or knot-recognition time is included.}
\label{tab:timings}
\end{table}
'''
(ROOT/'results/benchmark_table.tex').write_text(table)
rows=[]
for x in b['binary_stress']:
    rows.append(f"{x['parameter_exponent']:,} & $0\\times0$ & {x['output_bytes']:,} & {x['median_ms']:.3f} \\\\")
(ROOT/'results/binary_table.tex').write_text(r'''\begin{table}[ht]
\centering
\begin{tabular}{@{}rrrr@{}}
\toprule
$e$ in $N=2^e$ & Matrix & Serialized answer bytes & Median ms\\
\midrule
'''+ '\n'.join(rows)+r'''
\bottomrule
\end{tabular}
\caption{Binary stress tests, with genus/crosscaps and multiplicity both large. No expanded baseline or timing ratio is claimed.}
\label{tab:binary}
\end{table}
''')
