"""CAPPED literal oracles. None of the loops over ranks below is a binary-size
algorithm. These are for finite validation and explicitly labelled benchmarks.
"""
from __future__ import annotations
from collections import defaultdict
from itertools import combinations
from atlas import Atlas, validate, bits, mask_image, canonical_data
from sources import validate_pairings, permute_mask


def combinatorial_flags(poly) -> tuple[tuple[int,...], ...]:
    faces=poly.faces(); result=[]
    # Different from the producer's recursive maximal-carrier enumeration.
    for length in range(1,poly.dim+2):
        for chain in combinations(faces,length):
            if all(a!=b and a & ~b==0 for a,b in zip(chain,chain[1:])):
                result.append(chain)
    return tuple(result)


def expanded_cells(atlas: Atlas, cap: int = 500000):
    idx=validate(atlas)
    count=sum(f.hi-f.lo for f in atlas.families)
    if count>cap: raise ValueError('literal cell expansion cap')
    dim={}; facets={}; allfaces={}; marks=defaultdict(set)
    for f in atlas.families:
        p=idx.polys[f.poly]
        for i in range(f.lo,f.hi):
            cell=(f.name,i); dim[cell]=p.dim; local={}
            for g in p.faces():
                if g==p.full: continue
                c=next(c for c in idx.charts[f.name,g] if c.lo<=i<c.hi)
                local[g]=(c.lower,c.slope*i+c.shift)
            allfaces[cell]=local
            if len(p.vertices)==p.dim+1:
                facets[cell]=tuple(local[p.full^(1<<j)] for j in range(p.dim+1)) if p.dim else ()
            else: facets[cell]=tuple(local[g] for g in p.faces() if p.face_dim(g)==p.dim-1)
    for m in atlas.marks:
        for i in range(m.lo,m.hi): marks[m.label].add((m.family,i))
    return dim,facets,allfaces,dict(marks)


def literal_flags(source: Atlas, cap: int = 500000):
    idx=validate(source)
    local={p.name:combinatorial_flags(p) for p in source.polytopes}
    bytop={p.name:tuple(c for c in local[p.name] if c[-1]==p.full) for p in source.polytopes}
    count=sum((f.hi-f.lo)*len(bytop[f.poly]) for f in source.families)
    if count>cap: raise ValueError('literal flag expansion cap')
    dimensions={}; boundaries={}; marked=defaultdict(set)
    for f in source.families:
        p=idx.polys[f.poly]
        for i in range(f.lo,f.hi):
            for chain in bytop[f.poly]:
                key=(f.name,i,chain); dimensions[key]=len(chain)-1; out=[]
                if len(chain)>1:
                    for delete in range(len(chain)):
                        kept=chain[:delete]+chain[delete+1:]
                        if kept[-1]==p.full: target=(f.name,i,kept)
                        else:
                            c=next(c for c in idx.charts[f.name,kept[-1]] if c.lo<=i<c.hi)
                            target=(c.lower,c.slope*i+c.shift,tuple(mask_image(g,c.face,c.vertex_map) for g in kept))
                        out.append(target)
                boundaries[key]=tuple(out)
                for (label,name), intervals in idx.marks.items():
                    if name==f.name and any(lo<=i<hi for lo,hi in intervals): marked[label].add(key)
    return dimensions,boundaries,dict(marked)


def compare_compiled(source,certificate,cap=500000) -> dict:
    refdims,reffaces,refmarks=literal_flags(source,cap)
    dims,faces,allfaces,marks=expanded_cells(certificate.result,cap)
    carriers={c.output:c for c in certificate.carriers}
    mapping={x:(carriers[x[0]].source,x[1],carriers[x[0]].flag) for x in dims}
    assert {mapping[x]:d for x,d in dims.items()}==refdims
    assert {mapping[x]:tuple(mapping[y] for y in ys) for x,ys in faces.items()}==reffaces
    assert {label:{mapping[x] for x in xs} for label,xs in marks.items()}==refmarks
    regular_check(dims,faces,allfaces)
    return {'cells':len(dims),'covers':sum(len(x) for x in faces.values()),'marked_cells':sum(len(x) for x in marks.values())}


def regular_check(dimensions,facets,allfaces=None) -> None:
    vertices={}
    for cell in sorted(dimensions,key=lambda x:dimensions[x]):
        d=dimensions[cell]
        if d==0: vertices[cell]=frozenset((cell,)); continue
        fs=facets[cell]
        if len(fs)!=d+1 or len(set(fs))!=len(fs): raise AssertionError('nonregular facets')
        vs=frozenset().union(*(vertices[f] for f in fs)); vertices[cell]=vs
        if len(vs)!=d+1: raise AssertionError('vertices identify within a simplex')
        if any(dimensions[f]!=d-1 for f in fs): raise AssertionError('wrong face dimension')
        if allfaces is not None:
            if len(set(allfaces[cell].values()))!=(1<<(d+1))-2:
                raise AssertionError('distinct local faces identify')
            for mask,face in allfaces[cell].items():
                if len(vertices[face])!=len(bits(mask)): raise AssertionError('face vertex count')
    # Simplicial identities with the distinguished vertex order.
    for cell,fs in facets.items():
        if dimensions[cell]<2: continue
        for i in range(len(fs)):
            for j in range(i+1,len(fs)):
                if facets[fs[j]][i]!=facets[fs[i]][j-1]:
                    raise AssertionError('ordered face square fails')


def abstract_simplex_check(dimensions,facets) -> bool:
    verts={}; seen=set()
    for x in sorted(dimensions,key=lambda x:dimensions[x]):
        v=frozenset((x,)) if dimensions[x]==0 else frozenset().union(*(verts[y] for y in facets[x]))
        if v in seen: return False
        seen.add(v); verts[x]=v
    return True


def homology(dimensions,facets,p=2,selected=None):
    """Ordered simplex chains over F_p; valid for flags, NOT general polytopes."""
    if p not in (2,3,5,7): raise ValueError('oracle primes are 2,3,5,7')
    chosen=set(dimensions) if selected is None else set(selected)
    if any(y not in chosen for x in chosen for y in facets[x]): raise ValueError('selection is not a subcomplex')
    cells=[sorted((x for x in chosen if dimensions[x]==d),key=repr) for d in range(4)]
    ranks=[0]*5
    for d in range(1,4):
        rows={x:j for j,x in enumerate(cells[d-1])}; pivots={}
        for x in cells[d]:
            col={}
            for j,y in enumerate(facets[x]):
                r=rows[y]; col[r]=(col.get(r,0)+(-1 if j%2 else 1))%p
                if not col[r]: del col[r]
            while col:
                r=max(col)
                if r not in pivots:
                    inv=pow(col[r],-1,p); col={i:v*inv%p for i,v in col.items()}
                    pivots[r]=col; break
                c=col[r]
                for i,v in pivots[r].items():
                    col[i]=(col.get(i,0)-c*v)%p
                    if not col[i]: del col[i]
        ranks[d]=len(pivots)
    return tuple(len(cells[d])-ranks[d]-ranks[d+1] for d in range(4))


def source_flag_orbits(tetrahedra):
    """Direct finite flag quotient from tetrahedral face pairings.

    Does not call tetrahedral_atlas or the flag compiler. Full local flags,
    not their quotient vertex sets, are unioned across source face maps.
    """
    validate_pairings(tetrahedra)
    from atlas import simplex
    chains=combinatorial_flags(simplex(3))
    nodes=[(t,c) for t in range(len(tetrahedra)) for c in chains]
    parent={x:x for x in nodes}
    def find(x):
        while parent[x]!=x:
            parent[x]=parent[parent[x]]; x=parent[x]
        return x
    def union(a,b):
        a,b=find(a),find(b)
        if a!=b: parent[max(a,b)]=min(a,b)
    for t,row in enumerate(tetrahedra):
        for f,e in enumerate(row):
            if e is None: continue
            face=15^(1<<f)
            for c in chains:
                if c[-1] & ~face==0:
                    union((t,c),(e['tetrahedron'],tuple(permute_mask(g,e['permutation']) for g in c)))
    roots={x:find(x) for x in nodes}
    dims={r:len(r[1])-1 for r in roots.values()}
    facets={r:tuple(roots[r[0],r[1][:j]+r[1][j+1:]] for j in range(len(r[1]))) if len(r[1])>1 else () for r in dims}
    return roots,dims,facets


def compare_source_oracle(tetrahedra,metadata,certificate):
    roots,rdims,rfaces=source_flag_orbits(tetrahedra)
    dims,faces,allfaces,marks=expanded_cells(certificate.result)
    carriers={c.output:c for c in certificate.carriers}; mapping={}
    for cell in dims:
        c=carriers[cell[0]]; t,mask=metadata['representatives'][c.source]; v=bits(mask)
        chain=tuple(sum(1<<v[j] for j in bits(g)) for g in c.flag)
        mapping[cell]=roots[t,chain]
    assert len(set(mapping.values()))==len(dims)
    assert {mapping[x]:d for x,d in dims.items()}==rdims
    assert {mapping[x]:tuple(mapping[y] for y in ys) for x,ys in faces.items()}==rfaces
    regular_check(dims,faces,allfaces)
    return {'cells':len(dims),'covers':sum(len(x) for x in faces.values())}


def explicit_serializable(data):
    dims,faces,marks=data
    names={x:i for i,x in enumerate(sorted(dims,key=repr))}
    return {'cells':[{'id':names[x],'dim':dims[x],'faces':[names[y] for y in faces[x]]} for x in names],
            'marks':{label:sorted(names[x] for x in xs) for label,xs in marks.items()}}
