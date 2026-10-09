"""Separate complete enumeration and independently replayed disc discovery."""
from pathlib import Path
import json

ROOT=Path(__file__).resolve().parents[1]
data=json.loads((ROOT/'data/envelopes-benchmark.json').read_text())
tables={group:[r'\begin{center}',r'\small',r'\begin{tabular}{lrrrrr}',r'\toprule',
    r'Input & old ms & new ms & old/new & old A/A & new A/A\\',r'\midrule']
    for group in ('enumeration','discovery')}
for row in data['cases']:
    values=[v for s in row['samples']+row['warmups'] for v in s['measurements'].values()]
    assert all(v['completed'] and v['output_sha256']==values[0]['output_sha256'] for v in values)
    for arm in ('old','new'):
        values=[{k:v for k,v in s['measurements'][a].items() if k!='seconds'}
                for s in row['samples']+row['warmups'] for a in (arm,arm+'_AA')]
        assert all(v==values[0] for v in values)
    group,name=row['name'].split('/')
    if name=='empty-sector':label='Empty sector'
    else:
        _,n,typ=name.split('-');label=f'Base {n}, cap {typ}'
    cells=[label]+[f"{1000*row['medians'][a]:.3f}" for a in ('old','new')]
    cells += [f"{row['paired_ratios'][a]['median']:.3f}" for a in ('old_new','old_AA','new_AA')]
    tables[group].append(' & '.join(cells)+r'\\')
for group,lines in tables.items():
    lines += [r'\bottomrule',r'\end{tabular}',r'\end{center}']
    (ROOT/'tables'/f'envelopes_{group}.tex').write_text('\n'.join(lines)+'\n')
controls=[r['paired_ratios'][a]['median'] for r in data['cases'] for a in ('old_AA','new_AA')]
print(dict(envelope_measured=data['measured_calls'],warmups=data['warmup_calls'],AA_min=min(controls),AA_max=max(controls)))
