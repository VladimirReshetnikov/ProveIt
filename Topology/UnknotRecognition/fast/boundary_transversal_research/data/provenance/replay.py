"""Solver-free replay using original STANDARD equations, without Regina/Q elimination."""
import json
from math import gcd
from pathlib import Path
from fastunknot.normal_surface_geometry import _prepare,_EDGES
from euler_transversal_research.formal import formal_observation,rank
from euler_transversal_research.common import lower_fixtures,digest,source_hashes


def boundary_edges(p):
 return {p['edge_roots'][6*t+i] for t,f in p['boundary_faces']
         for i,(v,w) in enumerate(_EDGES) if v!=f and w!=f}


def checked_observation(source,rows):
 p=_prepare(source,lambda:None);assert p['vertices']==1
 value=formal_observation(p,rows)
 q=[x for row in rows for x in row[4:]]
 assert gcd(*q)==1
 support=[(t,q) for t,row in enumerate(rows) for q in range(3) if row[4+q]]
 # All triangle variables are retained. The projection kernel is exactly
 # the one-dimensional triangle-only vertex-link space. Thus Q-support
 # nullity is STANDARD nullity minus one, independently of Q cycle rows.
 columns=[7*t+v for t in range(len(rows)) for v in range(4)]
 columns += [7*t+4+q for t,q in support]
 R=rank([[eq.get(j,0) for j in columns] for eq in p['matching']])
 nullity=len(columns)-R-1
 assert nullity==1
 be=boundary_edges(p)
 value.update(support_size=len(support),support_rank=len(support)-nullity,
              support_nullity=nullity,vertices=p['vertices'],
              boundary_faces=[list(pair) for pair in p['boundary_faces']],
              boundary_edges=sorted(be),
              boundary_edge_tetrahedra=[t for t in range(len(rows)) if be.intersection(p['edge_roots'][6*t:6*t+6])])
 return value,R


def check_layer(before,step):
 after=step['source'];n=len(before['tetrahedra'])
 assert step['new_tetrahedron']==n and len(after['tetrahedra'])==n+1
 p,q=_prepare(before,lambda:None),_prepare(after,lambda:None)
 t,e=step['flipped_original_local_edge']
 assert type(t)is int and type(e)is int and 0<=t<n and 0<=e<6
 chosen=p['edge_roots'][6*t+e]
 assert chosen in boundary_edges(p)
 joins=[(f,r) for f,r in enumerate(after['tetrahedra'][n]) if r is not None]
 assert len(joins)==2
 attached={(r['tetrahedron'],r['permutation'][f]) for f,r in joins}
 assert attached==set(p['boundary_faces'])
 for i,row in enumerate(before['tetrahedra']):
  for f,r in enumerate(row):
   if (i,f) in attached:
    assert r is None and after['tetrahedra'][i][f]['tetrahedron']==n
   else:assert after['tetrahedra'][i][f]==r
 shared=sorted(set(range(4))-{f for f,r in joins})
 orientations=[]
 for f,r in joins:
  a,b=[r['permutation'][v] for v in shared]
  edge=_EDGES.index(tuple(sorted((a,b))))
  assert p['edge_roots'][6*r['tetrahedron']+edge]==chosen
  orientations.append(p['edge_orientations'][6*r['tetrahedron']+edge]^int(a>b))
 assert orientations[0]==orientations[1]
 mapping={}
 for before_edge,after_edge in zip(p['edge_roots'],q['edge_roots'][:6*n]):
  assert mapping.setdefault(before_edge,after_edge)==after_edge
 assert len(set(mapping.values()))==len(mapping),'layer merged original edge classes'
 assert {mapping[e] for e in boundary_edges(p)}-boundary_edges(q)=={mapping[chosen]}
 assert len(boundary_edges(q)-set(mapping.values()))==1
 assert q['vertices']==1 and q['edges']==p['edges']+1


root=Path('/tmp/boundary-transversal-design')
data=json.loads((root/'layer-refuter.json').read_text());fixtures={x['id']:x for x in lower_fixtures()}
pins=source_hashes();assert data['source_sha256']==pins
results=[]
for rec in data['records']:
 f=fixtures[rec['id']]
 assert rec['initial_source']==f['source']
 assert digest(f['source'])==rec['initial_source_sha256']==f['source_sha256']
 rows=f['witnesses'][rec['initial_witness_index']]['coordinates']
 assert rows==rec['initial_coordinates']
 obs,R=checked_observation(f['source'],rows);assert obs==rec['initial']
 source=f['source'];ranks=[]
 for step in rec['steps']:
  check_layer(source,step)
  assert step['coordinates'][:-1]==rows
  assert sum(bool(x) for x in step['coordinates'][-1][4:])<=1
  next_obs,R=checked_observation(step['source'],step['coordinates'])
  assert next_obs==step['observation']
  assert next_obs['canonical_euler']==obs['canonical_euler']>0
  assert next_obs['conflicts']==obs['conflicts']
  source,rows,obs=step['source'],step['coordinates'],next_obs
  ranks.append(R)
 assert digest(source)==rec['final_source_sha256']
 assert set(obs['conflicts']).isdisjoint(obs['boundary_edge_tetrahedra'])
 result=dict(id=rec['id'],source_sha256=digest(source),tetrahedra=len(rows),
             formal_euler=obs['canonical_euler'],conflicts=obs['conflicts'],
             boundary_faces=obs['boundary_faces'],boundary_edge_tetrahedra=obs['boundary_edge_tetrahedra'],
             q_support=obs['support_size'],q_support_rank=obs['support_rank'],q_support_nullity=1,
             original_standard_restricted_ranks=ranks,
             checked_layering_maps=len(rec['steps']),
             scope='valid finite oriented one-vertex torus-boundary supplied source; positive primitive Q-extreme ray; new layerings are not in maintained crushing-chain schema')
 results.append(result);print(result,flush=True)
assert source_hashes()==pins
(root/'replay.json').write_text(json.dumps(dict(passed=True,source_sha256=pins,regina_used=False,lp_used=False,
     q_cycle_model_used=False,records=results),indent=2)+'\n')
