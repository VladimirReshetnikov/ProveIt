"""One canonical 2-3 Pachner move on a finite torus-boundary manifold.

Replace two distinct tetrahedra across a paired face by the other filling
of their formal bipyramid. Boundary identifications may identify vertices;
the replacement is a PL homeomorphism relative to the formal boundary.
"""
from .normal_cocycle import _Budget
from .normal_surface_geometry import _prepare,NormalOrbitError


def pachner_23(triangulation, tetrahedron, face, *, max_work=None, check=lambda:None):
    """Return a fresh canonical replacement and its selected-face certificate.

    The caller supplies a finite orientable manifold with one torus boundary.
    Only the chosen local move is performed; no move search or diagram
    provenance is asserted. Exhaustion raises CocycleLimit before returning.
    """
    if type(tetrahedron) is not int or tetrahedron<0 or type(face) is not int or not 0<=face<4:
        raise ValueError('expected nonnegative tetrahedron index and face index 0..3')
    budget=_Budget(check,max_work)
    prepared=_prepare(triangulation,budget.tick);rows=prepared['tetrahedra'];n=len(rows)
    if tetrahedron>=n:raise ValueError('tetrahedron index is out of range')
    t,f=tetrahedron,face;r=rows[t][f]
    if r is None or r['tetrahedron']==t:
        raise NormalOrbitError('2-3 move requires two distinct tetrahedra across a paired face')
    u,p=r['tetrahedron'],r['permutation']
    left=[3]*4;right=[4]*4
    for label,v in enumerate(v for v in range(4) if v!=f):left[v]=label;right[p[v]]=label
    old={t:left,u:right};new=((3,4,0,1),(3,4,1,2),(3,4,2,0))
    survivors=[v for v in range(n) if v not in old];index={v:i for i,v in enumerate(survivors)};start=len(survivors)
    result=[]
    for v in survivors:
        budget.tick()
        result.append([None if r is None or r['tetrahedron'] in old else
                       dict(tetrahedron=index[r['tetrahedron']],permutation=list(r['permutation'])) for r in rows[v]])
    result.extend([[None]*4 for _ in new])
    facets={}
    for k,labels in enumerate(new):
        for a in range(4):facets.setdefault(tuple(sorted(labels[v] for v in range(4) if v!=a)),[]).append((start+k,a))
    def join(a,f,b,g,mapping):
        permutation=[g]*4
        for v,w in mapping:permutation[v]=w
        result[a][f]=dict(tetrahedron=b,permutation=permutation)
        result[b][g]=dict(tetrahedron=a,permutation=[permutation.index(v) for v in range(4)])
    for points,where in facets.items():
        budget.tick()
        if len(where)==2:
            (a,f),(b,g)=where
            join(a,f,b,g,[(new[a-start].index(v),new[b-start].index(v)) for v in points])
    boundary={}
    for v,labels in old.items():
        for a in range(4):
            if (v,a) in ((t,face),(u,p[face])):continue
            key=tuple(sorted(labels[w] for w in range(4) if w!=a))
            boundary[v,a]=facets[key][0]
    for (v,a),(target,b) in boundary.items():
        budget.tick();r=rows[v][a]
        if r is None:continue
        w,perm=r['tetrahedron'],r['permutation'];other_face=perm[a]
        if w in old:
            other,c=boundary[w,other_face]
            mapping=[(new[target-start].index(old[v][j]),new[other-start].index(old[w][perm[j]])) for j in range(4) if j!=a]
        else:
            other,c=index[w],other_face
            mapping=[(new[target-start].index(old[v][j]),perm[j]) for j in range(4) if j!=a]
        join(target,b,other,c,mapping)
    budget.tick()
    return dict(triangulation=dict(tetrahedra=result),
                certificate=dict(schema='pachner-23-v1',tetrahedron=t,face=face),
                stats=dict(work=budget.work,initial_tetrahedra=n,remaining_tetrahedra=n+1))
