"""Arbitrary-size compact Fibonacci layered solid tori, with exact meridians.

The face pairings match Regina Example3.lst(F_(n+1),F_(n+2)) but use no
fixed-width integer parameters.  The standard normal meridian has n occupied
quadrilateral types while its allowed quadrilateral sector has nullity one.
"""

from __future__ import annotations


def fibonacci_torus(tetrahedra):
    if type(tetrahedra) is not int or tetrahedra<1:
        raise ValueError("tetrahedra must be a positive integer")
    faces = [[None]*4 for _ in range(tetrahedra)]

    def join(source,face,target,permutation):
        opposite = permutation[face]
        inverse = [permutation.index(v) for v in range(4)]
        assert faces[source][face] is None
        assert faces[target][opposite] is None
        faces[source][face] = {"tetrahedron":target,"permutation":list(permutation)}
        faces[target][opposite] = {"tetrahedron":source,"permutation":inverse}

    for t in range(tetrahedra-1):
        join(t,0,t+1,[2,1,3,0])
        join(t,1,t+1,[0,3,1,2])
    join(tetrahedra-1,0,tetrahedra-1,[1,2,3,0])
    fib = [0,1]
    while len(fib)<=tetrahedra+5:
        fib.append(fib[-1]+fib[-2])
    rows = [[fib[tetrahedra-t+1],fib[tetrahedra-t+1],0,0,0,0,
             fib[tetrahedra-t]] for t in range(tetrahedra)]
    assert sum(map(sum,rows)) == fib[tetrahedra+5]-5
    return {
        "triangulation":{"tetrahedra":faces},"coordinates":rows,
        "quad_types":[2]*tetrahedra,
        "maximum_coordinate":fib[tetrahedra+1],
        "normal_disc_count":fib[tetrahedra+5]-5,
        "boundary_meridional_cuts":fib[tetrahedra+1:tetrahedra+4],
    }


def to_regina(raw):
    import regina
    t = regina.Triangulation3()
    for _ in raw["tetrahedra"]:
        t.newTetrahedron()
    for i,row in enumerate(raw["tetrahedra"]):
        for f,target in enumerate(row):
            if target is not None and t.tetrahedron(i).adjacentTetrahedron(f) is None:
                t.tetrahedron(i).join(f,t.tetrahedron(target["tetrahedron"]),
                                      regina.Perm4(*target["permutation"]))
    return t


if __name__ == "__main__":
    import json
    import regina
    checks = []
    for n in [1,2,3,4,8,12,16,24,32]:
        fixture = fibonacci_torus(n)
        t = to_regina(fixture["triangulation"])
        a,b,_ = fixture["boundary_meridional_cuts"]
        reference = regina.Example3.lst(a,b)
        assert t.isoSig() == reference.isoSig()
        qsurfaces = regina.NormalSurfaces(t,regina.NormalCoords.Quad)
        euler_one = [s for s in qsurfaces if str(s.eulerChar()) == "1"]
        assert len(euler_one) == 1
        coordinates = [[int(str(euler_one[0].triangles(i,v))) for v in range(4)]
                       +[int(str(euler_one[0].quads(i,q))) for q in range(3)]
                       for i in range(n)]
        assert coordinates == fixture["coordinates"]
        checks.append({"tetrahedra":n,"isosig":t.isoSig(),
                       "quad_vertex_count":len(qsurfaces),
                       "maximum_coordinate":fixture["maximum_coordinate"],
                       "normal_disc_count":fixture["normal_disc_count"]})
    print(json.dumps({"regina_version":regina.versionString(),
                      "independent_checks":checks},indent=2))
