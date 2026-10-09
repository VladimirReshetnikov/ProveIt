from fastunknot import Diagram
from fastunknot.diagram_exterior import diagram_exterior
from fastunknot.normal_cocycle import rank_one_cocycle_seed,local_coordinates
from fastunknot.normal_surface_geometry import _prepare,_coordinates,_EDGES
from fastunknot.cocycle_span import minimize_cocycle_span
import time
import json
from fastunknot.normal_cocycle import CocycleLimit
from pathlib import Path
for entry in json.loads(Path('../synthesis/data/cocycle-seed-audit.json').read_text())['cases']:
 s=entry['source']
 if entry['result']['status']=='UNKNOT' or len(s['pd'])>12:continue
 name=s['name'];d=Diagram.from_pd(s['pd'])
 try:
  raw=diagram_exterior(d);seed=rank_one_cocycle_seed(raw);p=_prepare(raw,lambda:None);edges={}
  for t,h in enumerate(seed['heights']):
   for j,(a,b) in enumerate(_EDGES):
    i=6*t+j;u,v=p['vertex_roots'][4*t+a],p['vertex_roots'][4*t+b];x=h[b]-h[a]
    if p['edge_orientations'][i]:u,v,x=v,u,-x
    edges[p['edge_roots'][i]]=(u,v,x)
  start=time.perf_counter();vs=[[u,u,v,v] for u,v,x in edges.values()];hs=[[0,0,x,x] for u,v,x in edges.values()]
  opt=minimize_cocycle_span(vs,hs,max_work=2000000);pot=dict(zip(opt['certificate']['vertex_ids'],opt['certificate']['potential']))
  heights=[[h+pot[v] for h,v in zip(hs,vs)] for hs,vs in zip(seed['heights'],seed['vertices'])]
  coords=[local_coordinates(row) for row in heights];a=_coordinates(p,coords,lambda:None)
  print(name,entry['source']['expected'],len(edges),a['euler_characteristic'],a['normal_disks'],time.perf_counter()-start,opt['stats']['work'],flush=True)
 except CocycleLimit: print(name,'CAP',flush=True)
