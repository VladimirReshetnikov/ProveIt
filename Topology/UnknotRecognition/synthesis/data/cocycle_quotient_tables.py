"""Measured original-model Euler pipelines and forced-cycle operation counts."""
import json
from pathlib import Path
root=Path(__file__).resolve().parents[1]
data=json.loads((root/'data/cocycle-quotient-benchmark.json').read_text())
labels={'trefoil':'Trefoil','optimized-positive':'Original disc','random-142':'Tied disc','random-19':'Random 19',
        'random-158':'Random 158','kinoshita_terasaka':'Kinoshita--Terasaka','circle-17':'Circle 17','circle-33':'Circle 33'}
lines=[r'\begin{tabular}{lrrrrr}',r'\toprule',r'Input & Full (ms) & Quotient (ms) & Full/new & Full A/A & New A/A \\',r'\midrule']
for row in data['cases']:
    assert all(v['count']==5 for v in row['paired_ratios'].values())
    ratios=[row['paired_ratios'][k]['median'] for k in ('old_new','old_AA','new_AA')]
    lines.append(labels[row['name']]+f" & {1000*row['medians']['old']:.3f} & {1000*row['medians']['new']:.3f} & "+' & '.join(f'{v:.3f}' for v in ratios)+r' \\')
lines += [r'\bottomrule',r'\end{tabular}']
(root/'tables/cocycle_quotient_benchmark.tex').write_text('\n'.join(lines)+'\n')
audit=json.loads((root/'data/cocycle-quotient-audit.json').read_text())
lines=[r'\begin{tabular}{rrrrr}',r'\toprule',r'$n$ & Full guards & New guards & Full scans & New augmentations \\',r'\midrule']
for row in audit['cycle_family']:
    a,b=row['results']['old'],row['results']['new']
    lines.append(f"{row['vertices']} & {a['work']:,} & {b['work']:,} & {a['stats']['arc_scans']:,} & {b['stats']['augmentations']}"+r' \\')
lines += [r'\bottomrule',r'\end{tabular}']
(root/'tables/cocycle_quotient_family.tex').write_text('\n'.join(lines)+'\n')
