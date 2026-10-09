"""Full-call measurements with the optimal-face fallback off and on."""
import json
from pathlib import Path
root=Path(__file__).resolve().parents[1]
data=json.loads((root/'data/cocycle-face-recognize.json').read_text())
labels={'circle-9':'Raw circle','optimized-positive':'Optimized positive',
        'random-99':'Early tree positive','random-81':'Late tree positive',
        'random-142':'New face positive','trefoil':'Trefoil','genus-one-miss':'Genus-one miss'}
lines=[r'\begin{tabular}{lrrrrr}',r'\toprule',
       r'Input & Off (ms) & On (ms) & Off/on & Off A/A & On A/A \\',r'\midrule']
for row in data['cases']:
    ratios=[row['paired_ratios'][k]['median'] for k in ('old_new','old_AA','new_AA')]
    assert all(row['paired_ratios'][k]['count']==5 for k in row['paired_ratios'])
    lines.append(labels[row['name']]+f" & {1000*row['medians']['old']:.3f} & {1000*row['medians']['new']:.3f} & "+' & '.join(f'{x:.3f}' for x in ratios)+r' \\')
lines += [r'\bottomrule',r'\end{tabular}']
(root/'tables/cocycle_face_recognize.tex').write_text('\n'.join(lines)+'\n')
