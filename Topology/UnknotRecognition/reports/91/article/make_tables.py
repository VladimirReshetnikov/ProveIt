#!/usr/bin/env python3
"""Regenerate article tables from the archived benchmark JSON, without rerunning timings."""
from pathlib import Path
import json, hashlib
p=Path(__file__).resolve().parents[1]
b=json.loads((p/'data/benchmark.json').read_text())
lines=[r'\begin{table}[ht]',r'\centering',r'\begin{tabular}{rrrrr}',r'\toprule',r'Copies $N$ & Vertices & Sparse (ms) & Literal (ms) & Literal/sparse\\',r'\midrule']
for x in b['ladders']:
 lines.append(f"{x['copies']} & {x['expanded_vertices']} & {x['a_median_ms']:.3f} & {x['b_median_ms']:.3f} & {x['b_over_a']:.2f}\\\\")
lines += [r'\bottomrule',r'\end{tabular}',r'\caption{Complete ladder-query medians. Ratios below one favor the literal path. No knot-recognition work is included.}',r'\label{tab:ladder}',r'\end{table}',r'\begin{table}[ht]',r'\centering',r'\begin{tabular}{rrrrrr}',r'\toprule',r'Arms $a$ & Root states & Indexed (ms) & Control (ms) & Time ratio & Work ratio\\',r'\midrule']
for x in b['stars']:
 lines.append(f"{x['arms_per_child']} & {x['root_states']:,} & {x['a_median_ms']:.3f} & {x['b_median_ms']:.3f} & {x['b_over_a']:.2f} & {x['unindexed_operations']/x['indexed_operations']:.2f}\\\\")
lines += [r'\bottomrule',r'\end{tabular}',r'\caption{Cost-indexed star joins versus the same producer without cost indexing. Time and work ratios are control/indexed. Work counts are logical candidate counts, not machine operations.}',r'\label{tab:stars}',r'\end{table}',r'\begin{table}[ht]',r'\centering',r'\begin{tabular}{rrrrr}',r'\toprule',r'Copies & Rules & Total states & Solve (ms) & Complete replay (ms)\\',r'\midrule']
for x in b['binary_stress']:
 lines.append(f"$2^{{{x['exponent_bits_minus_one']}}}$ & {x['rules']:,} & {x['total_states']:,} & {x['solve_median_ms']:.3f} & {x['complete_replay_ms']:.3f}\\\\")
lines += [r'\bottomrule',r'\end{tabular}',r'\caption{Binary ladder powers. Solve times are medians of five calls on a supplied grammar; complete replay is one separately timed call, with no claim of median precision. Peak table size is 32 in every row.}',r'\label{tab:binary}',r'\end{table}']
x,y=b['aa_controls']
lines.append(f"The two identical A/A controls had median B/A ratios {x['b_over_a']:.3f} and {y['b_over_a']:.3f}. These are empirical noise controls, not confidence intervals. The full raw repeat data are retained in \\mbox{{\\code{{data/benchmark.json}}}}.")
(p/'article/measurements.tex').write_text('\n'.join(lines)+'\n')
