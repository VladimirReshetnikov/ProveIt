#!/usr/bin/env python3
"""Generate article tables from the recorded full verification run."""
import json
from pathlib import Path
P=Path(__file__).resolve().parent
r=json.loads((P/'results.json').read_text())
lines=[r'\begin{table}[htbp]\centering\small',
       r'\begin{tabular}{rrrrr}\toprule',
       r'$n$ & $b_n$ & Observed $b_n\Prob(K_n=n)$ & Through $L_n^{-1}$ & Through $L_n^{-4}$\\\midrule']
for x in r['coefficient_rows']:
    lines.append(f"{x['n']:,} & {x['b']:.3f} & {x['b_times_p']:.9f} & {x['first']:.9f} & {x['fourth']:.9f} \\\\")
lines += [r'\bottomrule\end{tabular}',r'\caption{Coefficient diagnostics for the logarithmic tail at $\alpha=3/2$. The common leading approximation is $0.140260982\ldots$. These are floating-point diagnostics, not certified enclosures.}\label{tab:coeff}',r'\end{table}']
(P/'coefficient_table.tex').write_text('\n'.join(lines)+'\n')
lines=[r'\begin{table}[htbp]\centering\small',r'\begin{tabular}{rrrrr}\toprule',r'$n$ & Actual $M/b_n$ & Observed retained fraction & $\Phi_{3/2}$ & First correction\\\midrule']
for x in r['cutoff_rows']:
    if abs(x['s']-1)<.02:
        lines.append(f"{x['n']:,} & {x['s']:.6f} & {x['actual_ratio']:.9f} & {x['profile']:.9f} & {x['first']:.9f} \\\\")
lines += [r'\bottomrule\end{tabular}',r'\caption{Cutoff diagnostics with $M=\lfloor b_n\rfloor$ and $\lambda_n=0$. The first correction is $\Phi_{3/2}-(\log b_n)^{-1}\partial_\alpha\Phi_\alpha|_{\alpha=3/2}$.}\label{tab:cut}',r'\end{table}']
(P/'cutoff_table.tex').write_text('\n'.join(lines)+'\n')
lines=[r'\begin{table}[htbp]\centering\small',r'\begin{tabular}{rrrr}\toprule',r'$L$ & Exact-equation numerical $x/T$ & Through $L^{-1}$ & Through $L^{-2}$\\\midrule']
for x in r['inverse_rows']:
    lines.append(f"{x['L']} & {float(x['x_over_T']):.12f} & {float(x['first']):.12f} & {float(x['second']):.12f} \\\\")
lines += [r'\bottomrule\end{tabular}',r'\caption{Inverse-chart diagnostics. The displayed second-order approximation does not include the much smaller $R$-coordinate contribution.}\label{tab:inverse}',r'\end{table}']
(P/'inverse_table.tex').write_text('\n'.join(lines)+'\n')
print('Generated three tables.')
