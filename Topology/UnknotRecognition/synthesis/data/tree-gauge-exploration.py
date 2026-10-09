import json,random,time
from pathlib import Path
from fastunknot import Diagram
from fastunknot.diagram_exterior import diagram_exterior
from fastunknot.normal_cocycle import rank_one_cocycle_seed,local_coordinates
from fastunknot.normal_surface_geometry import _prepare,_coordinates,_EDGES
from fastunknot.normal_cocycle_verify import inspect_cocycle_certificate
sources=json.loads(Path('../synthesis/data/cocycle-seed-audit.json').read_text())['cases']
for item in sources:
 s=item['source']
 if s['name'] not in ['optimized-positive','gordian','survivor-00','survivor-01','survivor-02','unknot-genus-one'] and not s['name'].startswith('random-'):continue
 d=Diagram.from_pd(s['pd']);raw=diagram_exterior(d);seed=rank_one_cocycle_seed(raw);p=_prepare(raw,lambda:None)
 initial=_coordinates(p,seed['coordinates'],lambda:None)['euler_characteristic']
 if initial==1:continue
 edges={}
 for t,h in enumerate(seed['heights']):
  for j,(a,b) in enumerate(_EDGES):
   i=6*t+j;u,v=p['vertex_roots'][4*t+a],p['vertex_roots'][4*t+b];x=h[b]-h[a]
   if p['edge_orientations'][i]:u,v,x=v,u,-x
   edges[p['edge_roots'][i]]=(u,v,x)
 adj={v:[] for v in p['vertex_roots']}
 for e,(u,v,x) in edges.items():
  if u!=v:adj[u].append((v,x,e));adj[v].append((u,-x,e))
 roots=sorted(adj,key=lambda v:(-len(adj[v]),v));rng=random.Random(261009471)
 candidates=[]
 for trial in range(24):
  root=roots[trial%len(roots)]
  neighbors={v:list(a) for v,a in adj.items()}
  if trial>=4:
   for a in neighbors.values():rng.shuffle(a)
  pot={root:0};queue=[root]
  for u in queue:
   for v,x,e in neighbors[u]:
    if v not in pot:pot[v]=pot[u]+x;queue.append(v)
  h=[[x-pot[v] for x,v in zip(hs,vs)] for hs,vs in zip(seed['heights'],seed['vertices'])]
  c=[local_coordinates(row) for row in h]
  chi=_coordinates(p,c,lambda:None)['euler_characteristic'];candidates.append(chi)
  if chi==1:
   proof=dict(schema='diagram-cocycle-disc-v1',input_pd=[list(row) for row in d.pd],triangulation=raw,heights=h,coordinates=c,span_certificate=None)
   assert inspect_cocycle_certificate(d,proof)['compressing_discs']==1
   assert s['expected']=='UNKNOT'
   break
 print(s['name'],s['expected'],initial,max(candidates),len(candidates),candidates[:6],flush=True)
