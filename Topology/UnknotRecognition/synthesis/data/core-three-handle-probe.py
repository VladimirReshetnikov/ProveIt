"""Source dual-forest feasibility diagnostic; not an extra topology certificate.

Derive extreme edge-gap endpoints and delete candidate geometric 2/3 pairs.
Independent source replay of those deletions is still required before this
adapter may be used by the production whole-cut recognizer.
"""
from copy import deepcopy
import json
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'fast'))
from fastunknot.bundle_boundary_kernel import bundle_boundary_kernel
from fastunknot.normal_parallelity import normal_cut_parallelity
from fastunknot.parallelity_boundary_words import normal_parallelity_boundary_words
from fastunknot.normal_surface_geometry import _prepare, _coordinates, _EDGES
from normal_orbit_research.seeds import sources

pins=sources()
audit=json.loads((ROOT/'synthesis/data/boundary-kernel-audit.json').read_text())
selected={c['id']:c for c in audit['cases'] if c['native_reason']=='core_has_three_handles'}
bank=json.loads((ROOT/'fast/marked_parallelity_research/corpus.json').read_text())['cases']
records=[]
for c in bank:
    if c['id'] not in selected:continue
    p=normal_cut_parallelity(c['triangulation'],c['coordinates'])
    b=normal_parallelity_boundary_words(c['triangulation'],c['coordinates'])
    prepared=_prepare(c['triangulation'],lambda:None)
    analysed=_coordinates(prepared,c['coordinates'],lambda:None)
    g=deepcopy(p['geometry']); core=g['core']
    vertex_handle={h['vertex']:h['id'] for h in core['handles3']}
    ends={}
    for h in core['handles2']:
        t,j=divmod(h['edge'],6);u,v=_EDGES[j]
        # The root local edge has parity zero. Rank zero is its lower endpoint.
        assert prepared['edge_roots'][h['edge']]==h['edge']
        assert prepared['edge_orientations'][h['edge']]==0
        endpoints=[prepared['vertex_roots'][4*t+u],prepared['vertex_roots'][4*t+v]]
        weight=analysed['weights'][h['edge']]
        if weight:
            assert h['rank'] in (0,weight)
            endpoints=[endpoints[int(h['rank']==weight)]]
        ends[h['id']]=[vertex_handle[v] for v in endpoints if v in vertex_handle]
    alive=set(vertex_handle.values());remaining=set(ends);moves=[]
    while alive:
        choices=[(e,[v for v in ends[e] if v in alive]) for e in sorted(remaining)]
        choices=[(e,v[0]) for e,v in choices if len(v)==1]
        if not choices:break
        e,v=choices[0];remaining.remove(e);alive.remove(v)
        moves.append(dict(two_handle=e,three_handle=v))
    kernel=None
    if not alive:
        core['handles3']=[]
        core['handles2']=[dict(h,id=i) for i,h in enumerate(h for h in core['handles2'] if h['id'] in remaining)]
        kernel=bundle_boundary_kernel(g,p['summary'],b['skeleton'])
    reference=selected[c['id']]['regina'].get('histogram')
    census=None if kernel is None else kernel[1]['histogram']
    if census is not None:assert census==reference
    records.append(dict(id=c['id'],source_three_handles=len(vertex_handle),moves=moves,
                        remaining_three_handles=sorted(alive),kernel_eliminates_all_rows=kernel is not None,
                        candidate_histogram=census,oracle_histogram=reference))
    print(c['id'],'removed',len(moves),'kernel',kernel is not None,flush=True)
assert pins==sources()
report=dict(scope='Candidate 2/3 source reduction; no independent adapter certificate',
            native_source_sha256=pins,cases=records,
            all_three_handles_removed=sum(not c['remaining_three_handles'] for c in records),
            candidate_handlebody_censuses=sum(c['kernel_eliminates_all_rows'] for c in records))
Path(__file__).with_suffix('.json').write_text(json.dumps(report,indent=2)+'\n')
