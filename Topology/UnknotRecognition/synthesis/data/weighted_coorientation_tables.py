"""Validate complete outcomes and generate native/reference spectrum tables."""
from pathlib import Path
import json

ROOT=Path(__file__).resolve().parents[1]
data=json.loads((ROOT/'data/weighted-coorientation-benchmark.json').read_text())
names={'layered-8':'Layered 8','layered-32':'Layered 32','layered-64':'Layered 64',
    'layered-256':'Layered 256','layered-32-binary-scale':'Layered 32, binary scale',
    'empty':'Empty','vertex-link':'Vertex link','mobius':r'M\"obius band',
    'mobius-even':r'Even M\"obius multiple','mixed-components':'Mixed components',
    'binary-mixture':'Binary mixture','klein-torus':'Klein bottle'}
tables={group:[r'\begin{center}',r'\small',r'\begin{tabular}{lrrrrr}',r'\toprule',
    (r'Input & old ms & new ms & old/new & old A/A & new A/A\\'
     if group=='native' else r'Input & coord. ms & new ms & coord./new & coord. A/A & new A/A\\'),
    r'\midrule'] for group in ('native','coordinates')}
for row in data['cases']:
    values=[v for s in row['samples']+row['warmups'] for v in s['measurements'].values()]
    assert all(v['completed'] and v['spectrum_sha256']==values[0]['spectrum_sha256'] for v in values)
    for arm in ('old','new'):
        values=[{k:v for k,v in s['measurements'][a].items() if k!='seconds'}
                for s in row['samples']+row['warmups'] for a in (arm,arm+'_AA')]
        assert all(v==values[0] for v in values)
    group,name=row['name'].split('/')
    cells=[names[name]]+[f"{1000*row['medians'][a]:.3f}" for a in ('old','new')]
    cells += [f"{row['paired_ratios'][a]['median']:.3f}" for a in ('old_new','old_AA','new_AA')]
    tables[group].append(' & '.join(cells)+r'\\')
for group,lines in tables.items():
    lines += [r'\bottomrule',r'\end{tabular}',r'\end{center}']
    (ROOT/'tables'/f'weighted_coorientation_{group}.tex').write_text('\n'.join(lines)+'\n')
controls=[r['paired_ratios'][a]['median'] for r in data['cases'] for a in ('old_AA','new_AA')]
print(dict(weighted_coorientation_measured=data['measured_calls'],warmups=data['warmup_calls'],
           AA_min=min(controls),AA_max=max(controls)))
