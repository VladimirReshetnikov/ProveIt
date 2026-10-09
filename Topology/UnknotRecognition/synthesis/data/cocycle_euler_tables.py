"""Candidate-pipeline comparison: all root extrema versus exact Euler flow."""
import json
from pathlib import Path
root=Path(__file__).resolve().parents[1]
data=json.loads((root/'data/cocycle-euler-benchmark.json').read_text())
labels={'trefoil':'Trefoil','optimized-positive':'Original disc','random-142':'Tied disc',
        'random-19':'Random 19','random-158':'Random 158','kinoshita_terasaka':'Kinoshita--Terasaka'}
lines=[r'\begin{tabular}{lrrrrr}',r'\toprule',
       r'Input & Roots (ms) & Exact (ms) & Roots/exact & Roots A/A & Exact A/A \\',r'\midrule']
for row in data['cases']:
    assert all(v['count']==9 for v in row['paired_ratios'].values())
    ratios=[row['paired_ratios'][k]['median'] for k in ('old_new','old_AA','new_AA')]
    lines.append(labels[row['name']]+f" & {1000*row['medians']['old']:.3f} & {1000*row['medians']['new']:.3f} & "+' & '.join(f'{v:.3f}' for v in ratios)+r' \\')
lines += [r'\bottomrule',r'\end{tabular}']
(root/'tables/cocycle_euler_benchmark.tex').write_text('\n'.join(lines)+'\n')
