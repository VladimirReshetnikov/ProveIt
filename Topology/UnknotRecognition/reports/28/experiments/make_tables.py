"""Generate article data tables/macros directly from retained experiment JSON."""
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
b=json.loads((ROOT/'results/benchmarks.json').read_text())
a=json.loads((ROOT/'results/audit_summary.json').read_text())
names={'trefoil':'Trefoil','figure_eight':'Figure-eight','positive_2braid_11':'Positive two-braid, 11','coxeter_24':'Coxeter braid, 24','cancel_pairs_26':'Cancelling pairs, 26','trefoil_then_curls_6':'Trefoil + 6 curls','trefoil_then_curls_12':'Trefoil + 12 curls','trefoil_then_curls_24':'Trefoil + 24 curls'}
s=r'''\begin{table}[htbp]
\centering\small
\begin{tabular}{@{}lrrrrr@{}}
\toprule
Input & Full (ms) & Test (ms) & Reset (ms) & Full/reset & Gap $g$\\
\midrule
'''
for x in b['summary']:
 s+=f"{names[x['case']]} & {x['full_ms']:.3f} & {x['frontier_ms']:.3f} & {x['reset_ms']:.3f} & {x['full_over_reset']:.2f} & {x['reset_gap']}\\\\\n"
s+=r'''\bottomrule
\end{tabular}
\caption{Median paired raw-backend times, nine rounds. Test enables closure-summand bounds without resetting. Ratios below one mean the reset arm is slower. The full arm is the retained source-derived fixture, not the complete production recognizer.}
\label{tab:benchmark}
\end{table}
'''
(ROOT/'article/benchmark_table.tex').write_text(s)
tail=next(x for x in b['summary'] if x['case']=='trefoil_then_curls_24')
vals={'AuditQuivers':a['quiver_comparisons'],'AuditResets':a['reset_cases'],'AuditEarly':a['early_nontrivial'],'TailRatio':f"{tail['full_over_reset']:.2f}",'TailPeakFull':tail['full_peak'],'TailPeakReset':tail['reset_peak']}
(ROOT/'article/measurements.tex').write_text(''.join(f'\\newcommand{{\\{name}}}{{{value}}}\n' for name,value in vals.items()))
