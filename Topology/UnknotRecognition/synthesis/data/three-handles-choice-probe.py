"""Enumerate the four legal first pairs on each genuine one-vertex loop source.

This is a source-bound certificate experiment, not the native forest selector.
It exhibits the geometric dependence of the remaining raw cancellation test.
"""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT/'fast'))
from fastunknot.core_three_handle_reduction import reduce_core_three_handles
from fastunknot.core_handlebody import _forest, _occurrences
from fastunknot.core_three_handle_reduction_verify import replay_core_three_handles
from fastunknot.bundle_boundary_kernel import bundle_boundary_kernel
from fastunknot.normal_parallelity import normal_cut_parallelity
from fastunknot.parallelity_boundary_words import normal_parallelity_boundary_words
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
from normal_orbit_research.seeds import sources
pins=sources();fixture=ROOT/'fast/marked_parallelity_research/three_handle_corpus.json'
bank=json.loads(fixture.read_text())['cases'];records=[]
for c in bank:
    if c['id'] not in ('interior_loop/empty','interior_loop/boundary_link'):continue
    raw,rows=c['triangulation'],c['coordinates']
    p=normal_cut_parallelity(raw,rows,record_certificate=True)
    b=normal_parallelity_boundary_words(raw,rows,record_certificate=True);g=p['geometry']
    _,initial=reduce_core_three_handles(g)
    assert len(initial['cancellations'])==1
    trials=[]
    for edge in initial['dual_endpoints']:
        live=[v for v in edge['ends'] if v is not None]
        if len(live)!=1:continue
        e=edge['two_handle'];proof=deepcopy(initial)
        proof['cancellations']=[dict(two_handle=e,three_handle=live[0])]
        proof['surviving_two_handles']=[h['id'] for h in g['core']['handles2'] if h['id']!=e]
        reduced=replay_core_three_handles(g,proof);assert reduced is not None
        kernel=bundle_boundary_kernel(reduced,p['summary'],b['skeleton'])
        trial=dict(two_handle=e,complete=kernel is not None)
        if kernel is not None:
            certificate=dict(schema='normal-cut-handlebodies-v6',parallelity=p['certificate'],
                boundary=b['certificate'],core_reduction=proof,kernel=kernel[0],census=kernel[1])
            assert verify_normal_cut_handlebodies(raw,rows,certificate)
            trial.update(histogram=kernel[1]['histogram'],certificate_sha256=hashlib.sha256(
                json.dumps(certificate,sort_keys=True).encode()).hexdigest())
        trials.append(trial)
    forest,_=_forest(g['core'],lambda:None)
    counts=_occurrences(g['core'],forest,lambda:None)
    columns=sorted({h for row in counts.values() for h in row})
    records.append(dict(id=c['id'],native_first_pair=initial['cancellations'][0],trials=trials,
                        source_forest=forest,source_columns=columns,
                        source_matrix=[[row.get(h,0) for h in columns] for row in counts.values()]))
assert pins==sources()
report=dict(scope='Alternative forest experiment; native selection unchanged',native_source_sha256=pins,
            fixture_sha256=hashlib.sha256(fixture.read_bytes()).hexdigest(),cases=records)
Path(__file__).with_suffix('.json').write_text(json.dumps(report,indent=2)+'\n')
print([(r['id'],sum(t['complete'] for t in r['trials'])) for r in records])
