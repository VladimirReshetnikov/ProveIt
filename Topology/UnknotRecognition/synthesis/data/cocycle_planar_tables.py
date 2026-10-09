"""Generate complete-call planar-capping timing rows from the recorded run."""
import json
from pathlib import Path
root=Path(__file__).resolve().parents[1]
data=json.loads((root/'data/cocycle-planar-recognize.json').read_text())
labels={'circle-9':'Raw disc control','random-29':'Raw annulus control','optimized-positive':'Earlier seven-boundary proof',
        'random-1':'New four-tree positive','random-150':'Earlier raw planar proof','random-142':'Optimized annulus control',
        'random-25':'New extended positive A','random-162':'New extended positive B','random-176':'New extended positive C',
        'trefoil':'Trefoil miss','genus-one-miss':'Genus-one miss'}
lines=[r'\begin{tabular}{lrrrrr}',r'\toprule',r'Input & Off (ms) & On (ms) & Off/on & Off A/A & On A/A \\',r'\midrule']
for row in data['cases']:
    ratios=[row['paired_ratios'][k]['median'] for k in ('old_new','old_AA','new_AA')]
    assert all(row['paired_ratios'][k]['count']==5 for k in row['paired_ratios'])
    lines.append(labels[row['name']]+f" & {1000*row['medians']['old']:.3f} & {1000*row['medians']['new']:.3f} & "+' & '.join(f'{v:.3f}' for v in ratios)+r' \\')
lines += [r'\bottomrule',r'\end{tabular}']
(root/'tables/cocycle_planar_recognize.tex').write_text('\n'.join(lines)+'\n')
