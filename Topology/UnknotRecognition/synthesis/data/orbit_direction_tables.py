"""Generate sweep-direction evidence from complete paired results."""
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
audit=json.loads((ROOT/'data/orbit-direction-audit.json').read_text())
bench=json.loads((ROOT/'data/orbit-direction-benchmark.json').read_text())
for row in bench['cases']:
    values=[v for s in row['samples']+row['warmups'] for v in s['measurements'].values()]
    assert all(v['completed'] and v['topology_sha256']==values[0]['topology_sha256'] for v in values)
    for arm in ('old','new'):
        values=[{k:v for k,v in s['measurements'][a].items() if k!='seconds'}
                for s in row['samples']+row['warmups'] for a in (arm,arm+'_AA')]
        assert all(v==values[0] for v in values)
counts=[r'\begin{center}',r'\small',r'\begin{tabular}{rrrrrrr}',r'\toprule',
        r'$N$ & forward events & wide events & fwd. trans. & wide trans. & fwd. bytes & wide bytes\\',r'\midrule']
for row in audit['layered_family']:
    old,new=row['records']['forward'],row['records']['wide']
    values=[row['tetrahedra'],old['events'],new['events'],old['transmissions'],new['transmissions'],old['bytes'],new['bytes']]
    counts.append(' & '.join(map(str,values))+r'\\')
timings=[r'\begin{center}',r'\small',r'\begin{tabular}{lrrrrr}',r'\toprule',
         r'Supplied surface & forward ms & wide ms & paired factor & old A/A & new A/A\\',r'\midrule']
names={'layered-1':'Layered 1','layered-16':'Layered 16','layered-64':'Layered 64','layered-256':'Layered 256',
       'layered-64-binary-scale':'Layered 64, binary scale','empty':'Empty','mobius':r'M\"obius band',
       'vertex-link':'Vertex-link disc','finite_figureEight_relabel_1:6':'Relabelled figure-eight surface',
       'interior_finite_trefoil:97':'Interior trefoil surface','genus-two-coherent':'Genus-two coherent',
       '1275-supplied-surfaces':'Entire 1,275-vector batch'}
for row in bench['cases']:
    cells=[names[row['name']]]+[f"{1000*row['medians'][a]:.3f}" for a in ('old','new')]
    cells += [f"{row['paired_ratios'][a]['median']:.3f}" for a in ('old_new','old_AA','new_AA')]
    timings.append(' & '.join(cells)+r'\\')
for name,lines in [('orbit_direction_counts',counts),('orbit_direction_timings',timings)]:
    lines += [r'\bottomrule',r'\end{tabular}',r'\end{center}']
    (ROOT/'tables'/f'{name}.tex').write_text('\n'.join(lines)+'\n')
controls=[r['paired_ratios'][a]['median'] for r in bench['cases'] for a in ('old_AA','new_AA')]
print(dict(configurations=len(audit['configurations']),measured=bench['measured_calls'],warmups=bench['warmup_calls'],
           AA_min=min(controls),AA_max=max(controls)))
