"""Check paired complete outcomes and generate coorientation evidence tables."""
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
audit=json.loads((ROOT/'data/coorientation-audit.json').read_text())
bench=json.loads((ROOT/'data/coorientation-benchmark.json').read_text())
batch=json.loads((ROOT/'data/coorientation-corpus-benchmark.json').read_text())
for record in (bench,batch):
    for row in record['cases']:
        samples=[m for s in row['warmups']+row['samples'] for m in s['measurements'].values()]
        assert all(m['completed'] for m in samples)
        field='topology' if record is bench else 'topology_sha256'
        assert all(m[field]==samples[0][field] for m in samples)
        for arm in ('old','new'):
            values=[{k:v for k,v in s['measurements'][a].items() if k!='seconds'}
                    for s in row['warmups']+row['samples'] for a in (arm,arm+'_AA')]
            assert all(v==values[0] for v in values)

counts=[r'\begin{center}',r'\small',r'\begin{tabular}{rrrrrr}',r'\toprule',
        r'$N$ & old events & new events & sign bits & old bytes & new bytes\\',r'\midrule']
for row in audit['layered_family']:
    counts.append(' & '.join(str(row[k]) for k in ('tetrahedra','old_events','new_events','sign_entries','old_bytes','new_bytes'))+r'\\')

timings=[r'\begin{center}',r'\small',r'\begin{tabular}{lrrrrr}',r'\toprule',
         r'Supplied surface & old ms & new ms & old/new & old A/A & new A/A\\',r'\midrule']
names={'layered-1':'Layered 1','layered-16':'Layered 16','layered-64':'Layered 64',
       'layered-256':'Layered 256','layered-64-binary-scale':'Layered 64, binary scale',
       'empty':'Empty', 'mobius':r'M\"obius band','mobius-double':r'Doubled M\"obius band',
       'vertex-link':'Vertex-link disc','sphere_disc_mobius_mixture':'Sphere/disc/one-sided mixture',
       'sphere_plus_negative_chi':r'Sphere plus negative $\chi$', 'genus-two-coherent':'Genus-two coherent',
       '1275-supplied-surfaces':'Entire 1,275-vector batch'}
for row in bench['cases']+batch['cases']:
    cells=[names[row['name']]]+[f"{1000*row['medians'][a]:.3f}" for a in ('old','new')]
    cells += [f"{row['paired_ratios'][a]['median']:.3f}" for a in ('old_new','old_AA','new_AA')]
    timings.append(' & '.join(cells)+r'\\')
for name,lines in [('coorientation_counts',counts),('coorientation_timings',timings)]:
    lines += [r'\bottomrule',r'\end{tabular}',r'\end{center}']
    (ROOT/'tables'/f'{name}.tex').write_text('\n'.join(lines)+'\n')
print(dict(configurations=len(audit['cases']),derived=audit['derived'],
           measured_calls=bench['measured_calls'],batch_surface_calls=batch['measured_surface_calls']))
