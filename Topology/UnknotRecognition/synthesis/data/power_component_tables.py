"""Tables from complete new-operation A/A calls and paired pipeline controls."""
import json
from pathlib import Path
DATA=Path(__file__).resolve().parent
for mode in ('stages','source','pipeline'):
    d=json.loads((DATA/f'power-component-{mode}.json').read_text())
    pipeline=mode=='pipeline'
    lines=[r'\begin{center}\small',r'\begin{tabular}{lrrrrr}' if pipeline else r'\begin{tabular}{lrrr}',r'\toprule',
           r'Case & Old ms & New ms & Old/new & Old A/A & New A/A \\' if pipeline else r'Case & Current ms & A/A copy ms & Paired A/A \\',r'\midrule']
    for c in d['cases']:
        assert all(m['completed'] for s in c['samples']+c['warmups'] for m in s['measurements'].values())
        name=c['source']['name'].replace('_',r'\_');m=c['medians']
        if pipeline:
            r=c['paired_ratios'];values=[1000*m['old'],1000*m['current']]+[r[k]['median'] for k in ('current','old_AA','current_AA')]
        else:values=[1000*m['current'],1000*m['current_AA'],c['paired_AA']]
        lines.append(name+' & '+' & '.join(f'{x:.3f}' for x in values)+r' \\')
    lines += [r'\bottomrule',r'\end{tabular}',r'\end{center}']
    (DATA.parent/f'tables/power_component_{mode}.tex').write_text('\n'.join(lines)+'\n')
