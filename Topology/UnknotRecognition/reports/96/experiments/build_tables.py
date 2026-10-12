#!/usr/bin/env python3
"""Regenerate article tables from the frozen evidence, without rerunning tests."""
import json
from pathlib import Path
root=Path(__file__).resolve().parents[1]
r=json.loads((root/'evidence/results.json').read_text())
lines=[r'\begin{tabular}{rrrrrr}',r'\toprule',
       r'$m$ & Histories & Local rays & Kernel (ms) & Literal (ms) & Paired gain\\',r'\midrule']
for row in r['benchmark']['paired']:
    lines.append(f"{row['stages']} & {row['histories']:,} & {row['local_rays']} & "
                 f"{row['median_native_seconds']*1000:.3f} & {row['median_literal_seconds']*1000:.3f} & "
                 f"{row['median_paired_literal_native']:.3f}$\\times$\\\\")
lines.extend([r'\bottomrule',r'\end{tabular}'])
(root/'article/gain_table.tex').write_text('\n'.join(lines)+'\n')
lines=[r'\begin{tabular}{rrrrr}',r'\toprule',
       r'$m$ & Local rays & Candidate sets & Max. slope bits & Seconds\\',r'\midrule']
for row in r['benchmark']['large']:
    lines.append(f"{row['stages']} & {row['local_rays']:,} & {row['candidate_zero_sets']:,} & "
                 f"{row['maximum_message_numerator_bits']:,} & {row['seconds_single_run_not_paired']:.3f}\\\\")
lines.extend([r'\bottomrule',r'\end{tabular}'])
(root/'article/large_table.tex').write_text('\n'.join(lines)+'\n')
s=r['source_benchmark']
(root/'article/evidence_macros.tex').write_text(
    f"\\newcommand{{\\SourceOneTime}}{{{s['median_one_bag_seconds']:.6f}}}\n"
    f"\\newcommand{{\\SourceSplitTime}}{{{s['median_split_seconds']:.6f}}}\n"
    f"\\newcommand{{\\SourceGain}}{{{s['median_paired_one_bag_split']:.3f}}}\n"
    f"\\newcommand{{\\SourceControl}}{{{s['median_paired_control_one_bag']:.3f}}}\n"
    f"\\newcommand{{\\LastGain}}{{{r['benchmark']['paired'][-1]['median_paired_literal_native']:.2f}}}\n")
