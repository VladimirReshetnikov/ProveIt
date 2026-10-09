"""Generate sector timing tables only from complete, stable paired outcomes."""
from pathlib import Path
import json

ROOT=Path(__file__).resolve().parents[1]
data=json.loads((ROOT/'data/incoming-sectors-benchmark.json').read_text())
lines=[r'\begin{center}',r'\small',r'\begin{tabular}{lrrrrr}',r'\toprule',
       r'Supplied sector & dense ms & kernel ms & dense/kernel & dense A/A & kernel A/A\\',r'\midrule']
names={'layered-4':'Layered 4','layered-8':'Layered 8','layered-10':'Layered 10','empty':'Empty',
       'annulus':'Annular ray','one-sided':'One-sided ray','inessential-positive':'Inessential positive Euler'}
for row in data['cases']:
    values=[m for s in row['samples']+row['warmups'] for m in s['measurements'].values()]
    assert all(v['completed'] and v['status']==values[0]['status'] and v['coordinates']==values[0]['coordinates'] for v in values)
    for arm in ('old','new'):
        values=[{k:v for k,v in s['measurements'][a].items() if k!='seconds'} for s in row['samples']+row['warmups'] for a in (arm,arm+'_AA')]
        assert all(v==values[0] for v in values)
    cells=[names[row['name']]]+[f"{1000*row['medians'][a]:.3f}" for a in ('old','new')]
    cells += [f"{row['paired_ratios'][a]['median']:.3f}" for a in ('old_new','old_AA','new_AA')]
    lines.append(' & '.join(cells)+r'\\')
lines += [r'\bottomrule',r'\end{tabular}',r'\end{center}']
(ROOT/'tables/incoming_sectors_timings.tex').write_text('\n'.join(lines)+'\n')
print(dict(measured=data['measured_calls'],warmups=data['warmup_calls'],source_pins=len(data['source_sha256'])))
