"""Full-call paired timings for the annulus-cap criterion."""
import json
from pathlib import Path
root=Path(__file__).resolve().parents[1]
data=json.loads((root/'data/cocycle-annulus-recognize.json').read_text())
labels={'circle-9':'Raw disc control','optimized-positive':'Optimized disc control',
        'random-29':'Raw annulus, 4 crossings A','random-79':'Raw annulus, 4 crossings B',
        'random-99':'Raw annulus, 3 crossings','random-142':'New optimized annulus',
        'random-142-face-four':'Prior face-search positive','random-81':'Earlier late-tree positive',
        'random-1':'New tree annulus A','random-127':'New tree annulus B','trefoil':'Trefoil miss'}
lines=[r'\begin{tabular}{lrrrrr}',r'\toprule',r'Input & Off (ms) & On (ms) & Off/on & Off A/A & On A/A \\',r'\midrule']
for row in data['cases']:
    ratios=[row['paired_ratios'][k]['median'] for k in ('old_new','old_AA','new_AA')]
    assert all(row['paired_ratios'][k]['count']==9 for k in row['paired_ratios'])
    lines.append(labels[row['name']]+f" & {1000*row['medians']['old']:.3f} & {1000*row['medians']['new']:.3f} & "+' & '.join(f'{v:.3f}' for v in ratios)+r' \\')
lines += [r'\bottomrule',r'\end{tabular}']
(root/'tables/cocycle_annulus_recognize.tex').write_text('\n'.join(lines)+'\n')
