"""Regenerate genuine interior-vertex fixtures via topology-preserving moves.

Requires Regina only for regeneration. Tests consume the exported JSON.
The nested subdivisions force a dual boundary-forest chain. A 2-3 move at
an identified old face creates an interior loop with two equal endpoints.
"""
import json
from pathlib import Path
from normal_orbit_research.fixtures import (
    layered_torus, interior_vertex_torus, regina_triangulation, export_triangulation)


def main():
    import regina
    records=[]
    def save(t,name,sphere=False):
        raw=export_triangulation(t)
        boundary={v.index() for v in t.vertices() if v.isBoundary()}
        interior={v.index() for v in t.vertices() if not v.isBoundary()}
        fields=['empty','boundary_link']+(['interior_links'] if sphere else [])
        for field in fields:
            selected=boundary if field=='boundary_link' else interior if field=='interior_links' else set()
            rows=[[int(tet.vertex(v).index() in selected) for v in range(4)]+[0]*3
                  for tet in t.tetrahedra()]
            records.append(dict(id=name+'/'+field,triangulation=raw,coordinates=rows,
                                source_three_handles=len(interior)))
    raw,_=layered_torus(1);t=regina_triangulation(raw)
    for depth in range(1,13):
        tet=min(t.tetrahedra(),key=lambda x:sum(x.vertex(v).isBoundary() for v in range(4)))
        assert t.pachner(tet)
        if depth in (1,2,4,6,12):save(t,f'nested_1_4_{depth}',sphere=depth==6)
    raw,_=interior_vertex_torus();t=regina_triangulation(raw)
    for face in t.triangles():
        if face.degree()!=2:continue
        a,b=[(e.simplex(),e.vertices()[3]) for e in face.embeddings()]
        va,vb=a[0].vertex(a[1]),b[0].vertex(b[1])
        if va.index()==vb.index() and not va.isBoundary() and t.hasPachner(face):
            assert t.pachner(face)
            break
    else:raise AssertionError('no interior loop-producing move')
    assert any(e.vertex(0).index()==e.vertex(1).index() and not e.vertex(0).isBoundary() for e in t.edges())
    save(t,'interior_loop',sphere=True)
    path=Path(__file__).with_name('three_handle_corpus.json')
    path.write_text(json.dumps(dict(regina_version=regina.versionString(),cases=records),indent=2)+'\n')
    print(len(records),'genuine source fixtures')


if __name__=='__main__':main()
