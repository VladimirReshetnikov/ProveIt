"""Check a constructive positive-Euler relaxation at every anchor pattern.

The proof is uniform: put three quads in anchored tetrahedra and four
triangles in unanchored tetrahedra. Every face has one arc of each type,
every edge has weight two, and chi equals v+p-u. This is a formal LP vector,
not an admissible surface. Finite controls supplement the manuscript proof.
"""
from hashlib import sha256
import json
from pathlib import Path
import random
import sys

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'fast'))
from fastunknot.diagram import Diagram
from fastunknot.diagram_exterior import diagram_exterior
from fastunknot.diagram_exterior_verify import verify_diagram_exterior
from fastunknot.normal_surface_geometry import _prepare,_quad,_edge,_coordinates,NormalOrbitError
from normal_orbit_research.fixtures import layered_torus,interior_vertex_torus


def euler(prepared,rows):
    weights={}
    for t,row in enumerate(rows):
        for u in range(4):
            for v in range(u+1,4):
                value=row[u]+row[v]+sum(row[4:])-row[4+_quad(u,v)]
                root=prepared['edge_roots'][_edge(t,u,v)]
                assert weights.get(root,value)==value
                weights[root]=value
    boundary=sum(rows[t][v]+rows[t][4+_quad(f,v)] for t,f in prepared['boundary_faces']
                 for v in range(4) if v!=f)
    sides=sum(3*sum(row[:4])+4*sum(row[4:]) for row in rows)
    assert (sides+boundary)%2==0 and set(weights.values())=={2}
    return sum(weights.values())-(sides+boundary)//2+sum(map(sum,rows))


sources=[]
for name,strands,word in [('circle',1,[]),('curl',2,[1]),('cancelled-curl',2,[1,1,-1]),
                          ('trefoil',2,[1,1,1]),('figure-eight',3,[1,-2,1,-2]),
                          ('five-curl-chain',6,[1,2,3,4,5])]:
    diagram=Diagram.from_braid(strands,word);raw=diagram_exterior(diagram)
    assert verify_diagram_exterior(diagram,raw)
    sources.append((name,raw,max(1,len(word))))
for n in (1,2,4,8):sources.append((f'layered-{n}',layered_torus(n)[0],None))
sources.append(('interior-vertex',interior_vertex_torus()[0],None))
rng=random.Random(261009818)
cases=[]
for name,raw,crossings in sources:
    prepared=_prepare(raw,lambda:None)
    groups={}
    for corner,root in enumerate(prepared['vertex_roots']):groups.setdefault(root,[]).append(corner)
    boundary={prepared['vertex_roots'][4*t+v] for t,f in prepared['boundary_faces'] for v in range(4) if v!=f}
    v=len(groups);p=v-len(boundary);t=len(raw['tetrahedra']);b=len(prepared['boundary_faces'])
    assert len(boundary)==b//2
    samples=[]
    for selection in range(34):
        anchors=[corners[0] if selection==0 else corners[-1] if selection==1 else rng.choice(corners)
                 for corners in groups.values()]
        occupied={corner//4 for corner in anchors}
        rows=[[0,0,0,0,1,1,1] if i in occupied else [1,1,1,1,0,0,0] for i in range(t)]
        flat=[x for row in rows for x in row]
        assert all(sum(coefficient*flat[column] for column,coefficient in equation.items())==0
                   for equation in prepared['matching'])
        assert all(flat[7*(c//4)+c%4]==0 for c in anchors)
        chi=euler(prepared,rows)
        assert chi==v+p-len(occupied)>=p
        try:_coordinates(prepared,rows,lambda:None)
        except NormalOrbitError:pass
        else:raise AssertionError('incompatible relaxation accepted as a normal surface')
        if crossings is not None:
            assert (t,v,b,p)==(20*crossings,4*crossings+2,8*crossings,2)
            assert chi==4*crossings+4-len(occupied)>=2
        samples.append(dict(anchored_tetrahedra=len(occupied),formal_euler=chi))
    cases.append(dict(name=name,tetrahedra=t,vertices=v,interior_vertices=p,boundary_faces=b,
                      minimum_euler=min(s['formal_euler'] for s in samples),anchor_patterns=samples))
paths=['fast/fastunknot/diagram.py','fast/fastunknot/diagram_exterior.py',
    'fast/fastunknot/diagram_exterior_verify.py','fast/fastunknot/normal_surface_geometry.py',
    'fast/normal_orbit_research/fixtures.py','synthesis/data/anchored_relaxation.py']
result=dict(source_cases=len(cases),anchor_patterns=sum(len(c['anchor_patterns']) for c in cases),
    all_matching_and_anchor_checks_passed=True,all_vectors_rejected_as_incompatible=True,
    scope='formal unrestricted LP feasibility, not embedded normal surfaces or knot verdicts',
    cases=cases,source_sha256={p:sha256((ROOT/p).read_bytes()).hexdigest() for p in paths})
(ROOT/'synthesis/data/anchored-relaxation.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ('cases','source_sha256')}))
