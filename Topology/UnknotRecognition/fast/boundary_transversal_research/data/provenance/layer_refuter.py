"""Three exact boundary flips; compatible local ray extension and full replay."""
import json
from pathlib import Path
from fastunknot.normal_surface_geometry import _prepare,_EDGES,_quad
from fastunknot.normal_euler_verify import _reference_model
from euler_transversal_research.formal import formal_observation,rank
from euler_transversal_research.common import lower_fixtures,digest,source_hashes
from normal_crushing_research.fixtures import regina_triangulation,face_pairing


def observation(source,rows):
 p=_prepare(source,lambda:None)
 a=formal_observation(p,rows)
 C,*_=_reference_model(p,tuple((t,q) for t in range(len(rows)) for q in range(3)),lambda:None)
 q=[x for row in rows for x in row[4:]];S=[j for j,x in enumerate(q) if x]
 assert all(sum(x*y for x,y in zip(row,q))==0 for row in C)
 a.update(support_size=len(S),support_rank=rank([[row[j] for j in S] for row in C]))
 a['support_nullity']=a['support_size']-a['support_rank']
 be={p['edge_roots'][6*t+i] for t,f in p['boundary_faces'] for i,(v,w) in enumerate(_EDGES) if v!=f and w!=f}
 a.update(boundary_faces=p['boundary_faces'],boundary_edges=sorted(be),
          boundary_edge_tetrahedra=[t for t in range(len(rows)) if be.intersection(p['edge_roots'][6*t:6*t+6])],
          vertices=p['vertices'])
 return a


def extend(source,rows,chi):
 t=len(rows);faces=source['tetrahedra'][t]
 arcs=[]
 for f,rec in enumerate(faces):
  if rec is None:continue
  assert rec['tetrahedron']<t
  old=rows[rec['tetrahedron']];perm=rec['permutation'];of=perm[f]
  for v in range(4):
   if v!=f:arcs.append((f,v,old[perm[v]]+old[4+_quad(perm[v],of)]))
 candidates=[]
 for typ in range(3):
  for value in range(1+max(a for f,v,a in arcs)):
   triangles={};valid=True
   for f,v,a in arcs:
    x=a-int(typ==_quad(v,f))*value
    if x<0 or (v in triangles and triangles[v]!=x):valid=False;break
    triangles[v]=x
   if not valid:continue
   assert len(triangles)==4
   new=[triangles[v] for v in range(4)]+[value*int(q==typ) for q in range(3)]
   candidate=rows+[new];obs=observation(source,candidate)
   if obs['canonical_euler']==chi and obs['support_nullity']==1:
    candidates.append((value,typ,candidate,obs))
 assert candidates,'no preserving extreme extension'
 return min(candidates,key=lambda x:x[:2])[2:]

out=dict(source_sha256=source_hashes(),records=[])
for fixture in lower_fixtures():
 tri=regina_triangulation(fixture['source']);rows=fixture['witnesses'][0]['coordinates']
 originals=[]
 for edge in tri.edges():
  if edge.isBoundary():
   emb=edge.embedding(0);originals.append((emb.simplex().index(),emb.face()))
 record=dict(id=fixture['id'],initial_source=fixture['source'],initial_source_sha256=fixture['source_sha256'],
             initial_witness_index=0,initial_coordinates=rows,initial=observation(fixture['source'],rows),steps=[])
 for t,e in originals:
  edge=tri.tetrahedron(t).edge(e);assert edge.isBoundary()
  before=(t,e);new=tri.layerOn(edge)
  assert tri.isValid() and tri.isOrientable() and tri.countVertices()==1
  source=face_pairing(tri);rows,obs=extend(source,rows,record['initial']['canonical_euler'])
  record['steps'].append(dict(flipped_original_local_edge=before,new_tetrahedron=new.index(),source=source,coordinates=rows,observation=obs))
  print(fixture['id'],'layer',new.index(),'chi',obs['canonical_euler'],'nullity',obs['support_nullity'],'D',obs['conflicts'],'Bedge',obs['boundary_edge_tetrahedra'],flush=True)
 final=record['steps'][-1]
 assert set(final['observation']['conflicts']).isdisjoint(final['observation']['boundary_edge_tetrahedra'])
 assert final['observation']['canonical_euler']>0 and final['observation']['support_nullity']==1
 record['final_source_sha256']=digest(final['source']);out['records'].append(record)
Path('/tmp/boundary-transversal-design/layer-refuter.json').write_text(json.dumps(out,indent=2)+'\n')
