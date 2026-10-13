"""Scratch exact retained-root-ray tests of boundary conflict transversals."""
import json
from pathlib import Path
from itertools import combinations
from fastunknot.normal_surface_geometry import _prepare, _EDGES
from euler_transversal_research.common import lower_fixtures, source_hashes
from euler_transversal_research.formal import lower_bound_record

records=[]
for fixture in lower_fixtures():
 source=fixture['source']; prepared=_prepare(source,lambda:None)
 checked=lower_bound_record(source,fixture)
 boundary_faces=prepared['boundary_faces']
 boundary_tets=sorted({t for t,f in boundary_faces})
 boundary_edges=sorted({prepared['edge_roots'][6*t+i] for t,f in boundary_faces
                        for i,(v,w) in enumerate(_EDGES) if v!=f and w!=f})
 stars={e:sorted({t for t in range(len(source['tetrahedra']))
                 if e in prepared['edge_roots'][6*t:6*t+6]}) for e in boundary_edges}
 edge_tets=sorted(set().union(*map(set,stars.values())))
 observations=[]
 for i,witness in enumerate(fixture['witnesses']):
  conflict=set(witness['conflicts'])
  observations.append(dict(index=i,conflicts=sorted(conflict),
      canonical_euler=witness['canonical_euler'],support_rank=witness['support_rank'],
      support_size=witness['support_size'],
      avoids_boundary_faces=not bool(conflict.intersection(boundary_tets)),
      avoids_boundary_edges=not bool(conflict.intersection(edge_tets))))
 record=dict(id=fixture['id'],source=source,source_sha256=fixture['source_sha256'],
             checked_lower_bound=checked,boundary_faces=boundary_faces,
             boundary_tetrahedra=boundary_tets,boundary_edges=boundary_edges,
             boundary_edge_stars=stars,boundary_edge_tetrahedra=edge_tets,
             witnesses=observations)
 records.append(record)
 print(fixture['id'],'boundaryfaces',boundary_faces,'face_tets',boundary_tets,
       'boundaryedges',boundary_edges,'edge_tets',edge_tets,flush=True)
 print('face_refuters',[x for x in observations if x['avoids_boundary_faces']],flush=True)
 print('edge_refuters',[x for x in observations if x['avoids_boundary_edges']],flush=True)
Path('/tmp/boundary-transversal-design/probe.json').write_text(json.dumps(
 dict(source_sha256=source_hashes(),records=records),indent=2)+'\n')
