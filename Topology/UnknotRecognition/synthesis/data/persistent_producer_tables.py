"""Generate producer tables from retained complete-call measurements."""
import json
from pathlib import Path

DATA=Path(__file__).resolve().parent
TABLES=DATA.parent/'tables'
for mode in ('source','stages','pipeline'):
    data=json.loads((DATA/f'persistent-producer-{mode}.json').read_text())
    lines=[r'\begin{center}\small',r'\begin{tabular}{lrrrrr}',r'\toprule',
           r'Case & Old ms & New ms & Old/new & Old A/A & New A/A \\',r'\midrule']
    for row in data['cases']:
        assert all(m['completed'] for s in row['samples']+row['warmups'] for m in s['measurements'].values())
        name=row['source']['name'].replace('_',r'\_')
        med=row['medians'];ratios=row['paired_ratios']
        lines.append(f"{name} & {1000*med['old']:.3f} & {1000*med['current']:.3f} & "
                     f"{ratios['current']['median']:.3f} & {ratios['old_AA']['median']:.3f} & "
                     f"{ratios['current_AA']['median']:.3f} "+r'\\')
    lines += [r'\bottomrule',r'\end{tabular}',r'\end{center}']
    (TABLES/f'persistent_producer_{mode}.tex').write_text('\n'.join(lines)+'\n')
