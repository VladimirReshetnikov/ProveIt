#!/usr/bin/env python3
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
b=json.loads((ROOT/'data'/'benchmarks.json').read_text())
v=json.loads((ROOT/'data'/'validation.json').read_text())
lines=[r'\begin{table}[htbp]',r'\centering',r'\caption{Connected abstract examples: prepared-register analysis versus construction and rank of the explicit nonzero block. Seven randomized paired rounds. Times are milliseconds.}',r'\label{tab:abstract}',r'\begin{tabular}{rrrrrr}',r'\toprule',r'$m$ & Virtual dimension & Explicit & Register & Paired ratio & A/A \\',r'\midrule']
for x in b['abstract_examples']:
 lines.append(f"{x['register_length']} & {x['virtual_dimension']:,} & {1000*x['baseline_median_seconds']:.4f} & {1000*x['port_median_seconds']:.4f} & {x['paired_speedup_median']:.3f} & {x['aa_ratio_median']:.3f} \\\\")
lines += [r'\bottomrule',r'\end{tabular}',r'\end{table}',r'\begin{table}[htbp]',r'\centering',r'\caption{Compressed-only connected examples. No explicit competitor was run at these sizes; no speedup ratio is inferred.}',r'\label{tab:huge}',r'\begin{tabular}{rrrrrr}',r'\toprule',r'$m$ & Virtual dimension & Width & Ports & Time (ms) & Candidate rows \\',r'\midrule']
for x in b['compressed_only']:
 lines.append(f"{x['register_length']} & $2^{{{x['register_length']+1}}}$ & 4 & 1 & {1000*x['median_seconds']:.4f} & {x['candidate_rows']} \\\\")
lines += [r'\bottomrule',r'\end{tabular}',r'\end{table}',r'\begin{table}[htbp]',r'\centering',r'\caption{Negative controls on prepared small knot cubes. The treatment includes the explicit-to-port producer. Times are milliseconds; a ratio below one is a slowdown.}',r'\label{tab:cubes}',r'\begin{tabular}{lrrrrr}',r'\toprule',r'Presentation & Dimension & Ports & Direct & Bridge & Paired ratio \\',r'\midrule']
labels={'unknot_stabilized':'Stabilized unknot','trefoil':'Trefoil','figure_eight':'Figure-eight','unknot_relator':'Relator unknot'}
for x in b['small_knot_cube_bridge']:
 lines.append(f"{labels[x['name']]} & {x['dimension']} & {x['ports']} & {1000*x['baseline_median_seconds']:.4f} & {1000*x['port_median_seconds']:.4f} & {x['paired_speedup_median']:.4f} \\\\")
lines += [r'\bottomrule',r'\end{tabular}',r'\end{table}']
vals={x['register_length']:x['paired_speedup_median'] for x in b['abstract_examples']}
lines += [f'\\newcommand{{\\SlowFour}}{{{1/vals[4]:.1f}}}', f'\\newcommand{{\\GainTen}}{{{vals[10]:.3f}}}', f'\\newcommand{{\\GainTwelve}}{{{vals[12]:.2f}}}', f'\\newcommand{{\\GainFourteen}}{{{vals[14]:.2f}}}']
(ROOT/'article'/'measurements.tex').write_text('\n'.join(lines)+'\n')
print('Generated article/measurements.tex from recorded benchmark data.')
