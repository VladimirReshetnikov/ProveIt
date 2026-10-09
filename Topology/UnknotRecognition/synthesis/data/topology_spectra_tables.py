"""Validate complete paired topology outcomes and generate scope-specific tables."""
from pathlib import Path
import json

ROOT=Path(__file__).resolve().parents[1]
data=json.loads((ROOT/'data/topology-spectra-benchmark.json').read_text())
tables={key:[r'\begin{center}',r'\small',r'\begin{tabular}{lrrrrr}',r'\toprule',
    (r'Input & coord. ms & spectrum ms & coord./new & coord. A/A & new A/A\\'
     if key=='coordinates' else r'Input & direct ms & core ms & direct/core & direct A/A & core A/A\\'),r'\midrule']
    for key in ('coordinates','direct')}
names={'layered-8':'Layered 8','layered-32':'Layered 32','layered-64':'Layered 64',
       'layered-32-binary-scale':'Layered 32, binary scale','empty':'Empty','vertex-link':'Vertex link',
       'mobius':r'M\"obius band','mobius-even':r'Even M\"obius multiple',
       'mixed-components':'Mixed components','binary-mixture':'Binary mixture','klein-torus':'Klein bottle'}
for row in data['cases']:
    values=[v for s in row['samples']+row['warmups'] for v in s['measurements'].values()]
    assert all(v['completed'] and v['spectrum_sha256']==values[0]['spectrum_sha256'] for v in values)
    for arm in ('old','new'):
        values=[{k:v for k,v in s['measurements'][a].items() if k!='seconds'} for s in row['samples']+row['warmups'] for a in (arm,arm+'_AA')]
        assert all(v==values[0] for v in values)
    group,name=row['name'].split('/')
    cells=[names[name]]+[f"{1000*row['medians'][a]:.3f}" for a in ('old','new')]
    cells += [f"{row['paired_ratios'][a]['median']:.3f}" for a in ('old_new','old_AA','new_AA')]
    tables[group].append(' & '.join(cells)+r'\\')
for group,lines in tables.items():
    lines += [r'\bottomrule',r'\end{tabular}',r'\end{center}']
    name='coordinates' if group=='coordinates' else 'core'
    (ROOT/'tables'/f'topology_spectra_{name}.tex').write_text('\n'.join(lines)+'\n')
controls=[r['paired_ratios'][a]['median'] for r in data['cases'] for a in ('old_AA','new_AA')]
print(dict(measured=data['measured_calls'],warmups=data['warmup_calls'],AA_min=min(controls),AA_max=max(controls)))
