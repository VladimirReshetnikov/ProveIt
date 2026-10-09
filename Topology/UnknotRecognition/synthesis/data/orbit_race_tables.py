"""Validate complete paired race outcomes and render scope-specific tables."""
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
audit=json.loads((ROOT/'data/orbit-race-audit.json').read_text())
bench=json.loads((ROOT/'data/orbit-race-benchmark.json').read_text())
for row in bench['cases']:
    values=[v for s in row['samples']+row['warmups'] for v in s['measurements'].values()]
    assert all(v['completed'] and v['topology_sha256']==values[0]['topology_sha256'] for v in values)
    for arm in ('old','new'):
        values=[{k:v for k,v in s['measurements'][a].items() if k!='seconds'}
                for s in row['samples']+row['warmups'] for a in (arm,arm+'_AA')]
        assert all(v==values[0] for v in values)
counts=[r'\begin{center}',r'\small',r'\begin{tabular}{lrrrrr}',r'\toprule',
        r'Interval fixture & $W$ & attempt work $A$ & bound & attempts & total cycles\\',r'\midrule']
for r in audit['interval_cases'][-10:]:
    if r['rule']!='fine_wilf':continue
    name=f"Star {r['points']}" if r['points']!=72 else 'Switching graph'
    cells=[name,str(min(r['fixed_work'])),str(r['stats']['race_checkpoint_work']),str(r['attempt_bound']),
           str(r['stats']['race_attempts']),str(r['cycles'])]
    counts.append(' & '.join(cells)+r'\\')
groups={name:[r'\begin{center}',r'\small',r'\begin{tabular}{lrrrrr}',r'\toprule',
    r'Input & reference ms & race ms & ref./race & ref. A/A & race A/A\\',r'\midrule']
    for name in ('forward','wide')}
names={'layered-16':'Layered 16','layered-64':'Layered 64','layered-256':'Layered 256',
       'empty':'Empty','mobius':r'M\"obius band','vertex-link':'Vertex-link disc',
       'finite_figureEight_relabel_1:6':'Figure-eight surface',
       'interior_finite_trefoil:97':'Interior trefoil surface','1275-supplied-surfaces':'Entire 1,275-vector batch',
       'star-64':'Star 64 (interval kernel)','real-switch':'Switching graph (kernel)'}
for row in bench['cases']:
    group,name=row['name'].split('/')
    cells=[names[name]]+[f"{1000*row['medians'][a]:.3f}" for a in ('old','new')]
    cells += [f"{row['paired_ratios'][a]['median']:.3f}" for a in ('old_new','old_AA','new_AA')]
    groups['wide' if group=='kernel' else group].append(' & '.join(cells)+r'\\')
for name,lines in [('orbit_race_counts',counts)]+[(f'orbit_race_{k}',v) for k,v in groups.items()]:
    lines += [r'\bottomrule',r'\end{tabular}',r'\end{center}']
    (ROOT/'tables'/f'{name}.tex').write_text('\n'.join(lines)+'\n')
controls=[r['paired_ratios'][a]['median'] for r in bench['cases'] for a in ('old_AA','new_AA')]
print(dict(normal=len(audit['normal_cases']),intervals=len(audit['interval_cases']),measured=bench['measured_calls'],
           warmups=bench['warmup_calls'],AA_min=min(controls),AA_max=max(controls)))
