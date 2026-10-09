"""Full-call paired timings for shared cocycle discovery geometry."""
import json
from pathlib import Path
root=Path(__file__).resolve().parents[1]
data=json.loads((root/'data/cocycle-reuse-recognize.json').read_text())
labels={'circle-9':'Immediate disc','random-29':'Immediate annulus','optimized-positive':'Optimized disc',
        'random-142':'Optimized annulus','random-81':'Later tree annulus A','random-1':'Later tree annulus B',
        'planar-positive':'Early planar cap','planar-late':'Later planar cap','face-positive':'Optional face disc',
        'trefoil':'Trefoil miss','genus-one-miss':'Genus-one miss'}
lines=[r'\begin{tabular}{lrrrrr}',r'\toprule',r'Input & Old (ms) & New (ms) & Old/new & Old A/A & New A/A \\',r'\midrule']
for row in data['cases']:
    assert all(v['count']==9 for v in row['paired_ratios'].values())
    ratios=[row['paired_ratios'][k]['median'] for k in ('old_new','old_AA','new_AA')]
    lines.append(labels[row['name']]+f" & {1000*row['medians']['old']:.3f} & {1000*row['medians']['new']:.3f} & "+' & '.join(f'{v:.3f}' for v in ratios)+r' \\')
lines += [r'\bottomrule',r'\end{tabular}']
(root/'tables/cocycle_reuse_recognize.tex').write_text('\n'.join(lines)+'\n')
