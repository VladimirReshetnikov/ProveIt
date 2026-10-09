#!/usr/bin/env python3
"""Build manuscript tables from retained completed runs, without rerunning them."""
from pathlib import Path
import json
root = Path(__file__).resolve().parents[1]
b = json.loads((root/'data/benchmark.json').read_text())
lines = [r'\begin{tabular}{lrrrrrr}', r'\toprule',
         r'Family & $r$ & Lazy (ms) & Chained (ms) & Eager (ms) & C/L & E/L \\',r'\midrule']
for x in b['cases']:
    t=x['median_seconds']; p=x['paired_median_ratios']
    lines.append(f"{x['family']} & {x['rank']} & {1000*t['anchored']:.3f} & {1000*t['chained']:.3f} & {1000*t['anchored_eager']:.3f} & {p['chained_over_anchored']:.2f} & {p['eager_over_lazy']:.2f} "+r'\\')
lines += [r'\bottomrule',r'\end{tabular}']
(root/'data/benchmark_table.tex').write_text('\n'.join(lines)+'\n')
lines=[r'\begin{tabular}{lrrrr}',r'\toprule',r'Family & $r$ & Lazy A/A & Chained A/A & Chained nodes \\',r'\midrule']
for x in b['cases']:
    p=x['paired_median_ratios']; n=x['warmups']['chained']['metrics']['allocated_grammar_nodes']
    lines.append(f"{x['family']} & {x['rank']} & {p['anchored_A_over_A']:.3f} & {p['chained_A_over_A']:.3f} & {n} "+r'\\')
lines += [r'\bottomrule',r'\end{tabular}']
(root/'data/control_table.tex').write_text('\n'.join(lines)+'\n')
a=json.loads((root/'data/audit.json').read_text())
lines=[r'\begin{tabular}{rrrrrr}',r'\toprule',r'$r$ & $b$ & Exponent bits & Source nodes & Chained nodes & Proof bytes \\',r'\midrule']
for x in a['huge_exponent_cases']:
    n=x.get('chained_allocated_nodes',r'---')
    lines.append(f"{x['rank']} & {x['local_power_bits_parameter']} & {x['largest_image_exponent_bits']:,} & {x['source_nodes']:,} & {n} & {x['certificate_bytes']:,} "+r'\\')
lines += [r'\bottomrule',r'\end{tabular}']
(root/'data/capacity_table.tex').write_text('\n'.join(lines)+'\n')
