#!/usr/bin/env python3
"""Render the frozen JSON measurements into manuscript tables."""
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
r=json.loads((ROOT/'results/benchmark_all.json').read_text())
for name, title in [('matrix','Rows'),('transport','$p=s$')]:
    lines=[r'\begin{tabular}{rrrrr}',r'\toprule',
           title+r' & New (ms) & Reference (ms) & Paired ratio & A/A \\',r'\midrule']
    for q in r[name]:
        size=q['rows'] if name=='matrix' else q['passive_rows']
        lines.append(f"{size} & {q['new_median_ms']:.3f} & {q['old_median_ms']:.3f} & {q['paired_old_over_new']:.3f} & {q['control_old_over_old']:.3f} "+r'\\')
    lines += [r'\bottomrule',r'\end{tabular}']
    (ROOT/'article/tables'/f'{name}.tex').write_text('\n'.join(lines)+'\n')
lines=[r'\begin{tabular}{rrrr}',r'\toprule',
       r'$\log_2 N$ & Products & Serialized bytes & Complete query (ms) \\',r'\midrule']
for q in r['power']:
    lines.append(f"{q['half_length_exponent']} & {q['products']} & {q['serialized_bytes']:,} & {q['median_ms']:.3f} "+r'\\')
lines += [r'\bottomrule',r'\end{tabular}']
(ROOT/'article/tables/power.tex').write_text('\n'.join(lines)+'\n')
