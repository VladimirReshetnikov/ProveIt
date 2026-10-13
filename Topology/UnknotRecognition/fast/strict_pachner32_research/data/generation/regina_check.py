"""Fresh optional Regina validation of every retained native relative move."""
from hashlib import sha256
import json
from pathlib import Path
import regina

HERE=Path(__file__).resolve().parent

def convert(source):
    tri=regina.Triangulation3();tets=tri.newTetrahedra(len(source['tetrahedra']))
    for t,row in enumerate(source['tetrahedra']):
        for f,r in enumerate(row):
            if r is not None and tets[t].adjacentTetrahedron(f) is None:
                tets[t].join(f,tets[r['tetrahedron']],regina.Perm4(*r['permutation']))
    return tri

def summary(tri):
    assert tri.isValid() and tri.isOrientable()
    assert tri.countComponents()==1 and tri.countVertices()==1
    assert tri.countBoundaryComponents()==1 and tri.boundaryComponent(0).eulerChar()==0
    return dict(tetrahedra=tri.size(),vertices=1,boundary_components=1,boundary_euler=0,
                valid=True,orientable=True,iso_sig=tri.isoSig())

def main():
    path=HERE/'scan.json';raw=path.read_bytes();scan=json.loads(raw)
    out=dict(regina=regina.versionString(),scan_file_sha256=sha256(raw).hexdigest(),records=[],passed=False)
    for record in scan['records']:
        source=record['initial_source'];steps=[];initial=summary(convert(source))
        for step in record['steps']:
            tri=convert(source);candidate=step['candidate'];t=candidate['tetrahedron'];a,b=candidate['vertices']
            edge=tri.tetrahedron(t).edge(regina.Edge3.edgeNumber[a][b]);assert edge.degree()==3 and not edge.isBoundary()
            accepted=tri.pachner(edge);assert accepted
            native=convert(step['successor']);native_summary=summary(native);regina_summary=summary(tri)
            iso=tri.isIsomorphicTo(native);assert iso is not None
            maps=[dict(tetrahedron=iso.simpImage(i),vertices=[iso.facetPerm(i)[j] for j in range(4)]) for i in range(tri.size())]
            steps.append(dict(candidate=candidate,regina_accepted=True,native=native_summary,regina=regina_summary,
                              labelled_equal=tri==native,isomorphic=True,isomorphism=maps))
            source=step['successor']
        out['records'].append(dict(id=record['id'],initial=initial,steps=steps,final=summary(convert(source))))
        print(record['id'],len(steps),'Regina moves agree; labelled equality', [s['labelled_equal'] for s in steps],flush=True)
    out['passed']=True;(HERE/'regina-check.json').write_text(json.dumps(out,indent=2)+'\n')

if __name__=='__main__':main()
