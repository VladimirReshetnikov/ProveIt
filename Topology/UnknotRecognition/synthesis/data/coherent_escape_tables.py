"""Verify complete paired outcomes and render scope-separated timing tables."""
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
data=json.loads((ROOT/'data/coherent-escape-benchmark.json').read_text())
for row in data['cases']:
    samples=[m for s in row['warmups']+row['samples'] for m in s['measurements'].values()]
    assert all(m['completed'] for m in samples)
    if row['name'].startswith(('canonical','recognize')):
        records=[{k:v for k,v in m.items() if k!='seconds'} for m in samples]
        assert all(r==records[0] for r in records)
    else:
        assert len({m['coordinates_sha256'] for m in samples})==1
        assert all(m.get('topology')==samples[0].get('topology') for m in samples)
        for arm in ('old','new'):
            records=[{k:v for k,v in s['measurements'][a].items() if k!='seconds'}
                     for s in row['warmups']+row['samples'] for a in (arm,arm+'_AA')]
            assert all(r==records[0] for r in records)
        old=row['samples'][0]['measurements']['old']['stats']
        new=row['samples'][0]['measurements']['new']['stats']
        assert new['work']==5*old['augmentations']+3 and new['network_nodes']==0
    if row['name'].startswith('distinct'):
        old=row['samples'][0]['measurements']['old']['stats']
        assert old['dijkstra_searches']==old['augmentations']-1

def timing(row):
    return f"{1000*row['medians']['old']:.3f} & {1000*row['medians']['new']:.3f} & {row['paired_ratios']['old_new']['median']:.3f}"

kernel=[r'\begin{center}',r'\small',r'\begin{tabular}{rrrrrr}',r'\toprule',
        r'$N$ & old ms & new ms & paired factor & old guards & new guards\\',r'\midrule']
pipeline=[r'\begin{center}',r'\small',r'\begin{tabular}{lrrr}',r'\toprule',
          r'Complete measured operation & old ms & new ms & paired factor\\',r'\midrule']
names={'layered-16':'Layered 16: coherent analysis','layered-64':'Layered 64: coherent analysis',
       'layered-256':'Layered 256: coherent analysis','genus-two-miss':'Genus-two miss: coherent analysis',
       'escaped-disc':'Escaped disc: coherent analysis','canonical-control-1':'Canonical 1: coherent analysis',
       'canonical-control-4':'Canonical 4: coherent analysis','recognize-disc':'Diagram recognition: native disc',
       'recognize-miss':'Diagram recognition: fallback unknot','recognize-trefoil':'Diagram recognition: trefoil'}
for row in data['cases']:
    if row['name'].startswith('distinct'):
        stats=row['samples'][0]['measurements']
        n=int(row['name'].split('-')[-1])
        kernel.append(f"{n} & {timing(row)} & {stats['old']['stats']['work']} & {stats['new']['stats']['work']}"+r'\\')
    else:
        pipeline.append(names[row['name']]+' & '+timing(row)+r'\\')
for name,lines in [('coherent_escape_kernel',kernel),('coherent_escape_pipeline',pipeline)]:
    lines.extend([r'\bottomrule',r'\end{tabular}',r'\end{center}'])
    (ROOT/'tables'/f'{name}.tex').write_text('\n'.join(lines)+'\n')
controls=[r['paired_ratios'][a]['median'] for r in data['cases'] for a in ('old_AA','new_AA')]
print(dict(measured=data['measured_calls'],warmups=data['warmup_calls'],seconds=data['seconds'],AA_min=min(controls),AA_max=max(controls)))
