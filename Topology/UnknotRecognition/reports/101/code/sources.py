"""Source constructions for exact polytopes, finite face-paired tetrahedra,
and binary products with an interval/circle.

The tetrahedral importer checks pairing consistency and absence of face
holonomy; it does NOT claim general 3-manifold recognition. The one-tet
solid-torus example is the exact source in the pinned ProveIt fixture.
"""
from __future__ import annotations
from itertools import combinations
from collections import deque
from atlas import Atlas,Polytope,Family,Chart,Mark,simplex,bits,mask_image,rank,validate,integers


def face_polytope(poly: Polytope,face: int,name: str) -> Polytope:
    points=tuple(poly.vertices[i] for i in bits(face)); d=poly.face_dim(face)
    if d==0: return Polytope(name,((),))
    p0=points[0]
    axes=next(cols for cols in combinations(range(poly.dim),d)
              if rank(tuple(tuple(p[j]-p0[j] for j in cols) for p in points[1:]))==d)
    return Polytope(name,tuple(tuple(p[j] for j in axes) for p in points))


def polytope_ball(poly: Polytope, copies: int = 1) -> Atlas:
    integers(copies)
    if copies<=0: raise ValueError('positive number of copies required')
    faces=poly.faces(); pp={f:face_polytope(poly,f,f'P{f:x}') for f in faces}
    families=tuple(Family(f'C{f:x}',pp[f].name,0,copies) for f in faces)
    charts=[]
    for f in faces:
        local_vertices=bits(f)
        for g in pp[f].faces():
            if g==pp[f].full: continue
            global_face=sum(1<<local_vertices[j] for j in bits(g))
            charts.append(Chart(f'C{f:x}',g,0,copies,f'C{global_face:x}',1,0,tuple(range(len(bits(g))))))
    marks=tuple(Mark('boundary',f'C{f:x}',0,copies) for f in faces if f!=poly.full)
    return Atlas(tuple(pp.values()),families,tuple(charts),marks)


def line(n: int, periodic: bool = False) -> Atlas:
    integers(n)
    if n<=0: raise ValueError('line length must be positive')
    vertices=n if periodic else n+1
    fam=(Family('V','D0',0,vertices),Family('E','D1',0,n))
    charts=[Chart('E',1,0,n,'V',1,0,(0,))]
    if periodic:
        if n>1: charts.append(Chart('E',2,0,n-1,'V',1,1,(0,)))
        charts.append(Chart('E',2,n-1,n,'V',1,1-n,(0,)))
        marks=()
    else:
        charts.append(Chart('E',2,0,n,'V',1,1,(0,)))
        marks=(Mark('boundary','V',0,1),Mark('boundary','V',n,n+1))
    return Atlas((simplex(0),simplex(1)),fam,tuple(charts),marks)


def product_with_line(base: Atlas,n: int,periodic: bool=False) -> Atlas:
    """Base must be a finite singleton-rank atlas of dimension <=2.

    Output represents |base| x [0,n] or |base| x S^1, in O(base-size)
    records and O(log n) coordinate bits. Each local product is an exact
    convex polytope. 'boundary' is the topological product boundary only
    when base's boundary mark has that authenticated geometric meaning.
    """
    bi=validate(base)
    if any(f.lo!=0 or f.hi!=1 for f in base.families) or any(p.dim>2 for p in base.polytopes):
        raise ValueError('base must have singleton ranks and dimension <=2')
    interval=line(n,periodic); li=validate(interval)
    polys=[]; fam=[]; charts=[]; marks=[]; names={}; templates={}
    for bf in base.families:
        p=bi.polys[bf.poly]
        for lf in interval.families:
            q=li.polys[lf.poly]
            name=f'{bf.name}*{lf.name}'; pname=f'P:{name}'
            points=tuple(x+y for x in p.vertices for y in q.vertices)
            r=Polytope(pname,points); r.faces()
            names[bf.name,lf.name]=name; templates[bf.name,lf.name]=r
            polys.append(r); fam.append(Family(name,pname,lf.lo,lf.hi))
    for bf in base.families:
        p=bi.polys[bf.poly]
        for lf in interval.families:
            q=li.polys[lf.poly]; r=templates[bf.name,lf.name]; name=names[bf.name,lf.name]; nq=len(q.vertices)
            for face in r.faces():
                if face==r.full: continue
                pairs=[divmod(v,nq) for v in bits(face)]
                a=sum(1<<x for x in {x for x,y in pairs}); b=sum(1<<y for y in {y for x,y in pairs})
                if set(pairs)!={(x,y) for x in bits(a) for y in bits(b)}:
                    raise ArithmeticError('convex product face is not Cartesian')
                bc=[None] if a==p.full else bi.charts[bf.name,a]
                lc=[None] if b==q.full else li.charts[lf.name,b]
                for cb in bc:
                    lower_b=bf.name if cb is None else cb.lower
                    bm={x:x for x in bits(a)} if cb is None else dict(zip(bits(a),cb.vertex_map))
                    for cl in lc:
                        lower_l=lf.name if cl is None else cl.lower
                        lm={y:y for y in bits(b)} if cl is None else dict(zip(bits(b),cl.vertex_map))
                        lower_nq=len(li.polys[li.families[lower_l].poly].vertices)
                        vm=tuple(bm[x]*lower_nq+lm[y] for x,y in pairs)
                        lo,hi,s,t=(lf.lo,lf.hi,1,0) if cl is None else (cl.lo,cl.hi,cl.slope,cl.shift)
                        charts.append(Chart(name,face,lo,hi,names[lower_b,lower_l],s,t,vm))
            # Union of base-boundary x line and base x interval-boundary;
            # avoid duplicate intervals when both apply.
            if bi.marks.get(('boundary',bf.name)):
                marks.append(Mark('boundary',name,lf.lo,lf.hi))
            else:
                for lo,hi in li.marks.get(('boundary',lf.name),[]): marks.append(Mark('boundary',name,lo,hi))
    return Atlas(tuple(polys),tuple(fam),tuple(charts),tuple(marks))


def validate_pairings(tetrahedra: list) -> None:
    if not isinstance(tetrahedra,list) or not tetrahedra: raise ValueError('empty tetrahedral source')
    for t,row in enumerate(tetrahedra):
        if not isinstance(row,list) or len(row)!=4: raise ValueError('four faces required')
        for f,entry in enumerate(row):
            if entry is None: continue
            if not isinstance(entry,dict) or set(entry)!={'tetrahedron','permutation'}: raise ValueError('bad face gluing')
            u,p=entry['tetrahedron'],entry['permutation']; integers(u,*p)
            if not 0<=u<len(tetrahedra) or sorted(p)!=[0,1,2,3]: raise ValueError('bad gluing permutation')
            g=p[f]
            if (u,g)==(t,f): raise ValueError('a face cannot be paired to itself')
            partner=tetrahedra[u][g]
            if partner is None or partner['tetrahedron']!=t or any(partner['permutation'][p[i]]!=i for i in range(4)):
                raise ValueError('face pairings are not reciprocal')


def permute_mask(mask: int,p: list[int] | tuple[int,...]) -> int:
    return sum(1<<p[v] for v in bits(mask))


def tetrahedral_atlas(tetrahedra: list) -> tuple[Atlas,dict]:
    """Finite source importer. Returns atlas plus exact local representative charts."""
    validate_pairings(tetrahedra)
    nodes=[(t,m) for t in range(len(tetrahedra)) for m in range(1,16)]
    adjacency={v:[] for v in nodes}
    for t,row in enumerate(tetrahedra):
        for f,entry in enumerate(row):
            if entry is None: continue
            u,p=entry['tetrahedron'],tuple(entry['permutation']); face=15^(1<<f)
            for m in range(1,16):
                if m & ~face==0:
                    adjacency[t,m].append(((u,permute_mask(m,p)),p))
    root_of={}; maps={}; representatives=[]
    for root in nodes:
        if root in root_of: continue
        representatives.append(root); root_of[root]=root; maps[root]=tuple(range(len(bits(root[1]))))
        queue=deque([root])
        while queue:
            a=queue.popleft(); amap=dict(zip(bits(a[1]),maps[a]))
            for b,p in adjacency[a]:
                inverse={p[v]:v for v in bits(a[1])}
                bm=tuple(amap[inverse[w]] for w in bits(b[1]))
                if b in maps:
                    if root_of[b]!=root or maps[b]!=bm: raise ValueError('nontrivial local-face holonomy')
                else:
                    root_of[b]=root; maps[b]=bm; queue.append(b)
    names={r:f'C{j}' for j,r in enumerate(representatives)}
    families=tuple(Family(names[r],f'D{len(bits(r[1]))-1}',0,1) for r in representatives)
    charts=[]
    for r in representatives:
        t,m=r; rv=bits(m)
        for g in range(1,1<<len(rv)):
            if g==(1<<len(rv))-1: continue
            gm=sum(1<<rv[j] for j in bits(g)); occurrence=(t,gm)
            charts.append(Chart(names[r],g,0,1,names[root_of[occurrence]],1,0,maps[occurrence]))
    boundary=set()
    for t,row in enumerate(tetrahedra):
        for f,entry in enumerate(row):
            if entry is None:
                face=15^(1<<f)
                for m in range(1,16):
                    if m & ~face==0: boundary.add(names[root_of[t,m]])
    atlas=Atlas(tuple(simplex(d) for d in range(4)),families,tuple(charts),tuple(Mark('boundary',name,0,1) for name in sorted(boundary)))
    validate(atlas)
    metadata={'representatives':{names[r]:r for r in representatives},'root_of':root_of,'maps':maps}
    return atlas,metadata


def solid_torus_source() -> list:
    # Pinned native fixture: parallelity-admissibility-obstruction.json,
    # Git blob 2ea36d9d629c133e540cce4802ef76aa7342b2af.
    return [[{'tetrahedron':0,'permutation':[1,2,3,0]},
             {'tetrahedron':0,'permutation':[3,0,1,2]},None,None]]


def relabel_tetrahedra(source: list,permutations: list[tuple[int,...]],order: list[int]) -> list:
    validate_pairings(source)
    n=len(source)
    if sorted(order)!=list(range(n)) or len(permutations)!=n or any(sorted(p)!=[0,1,2,3] for p in permutations):
        raise ValueError('invalid relabelling')
    result=[[None]*4 for _ in range(n)]
    for t,row in enumerate(source):
        a=permutations[t]; inv={a[v]:v for v in range(4)}
        for f,e in enumerate(row):
            if e is not None:
                u,p=e['tetrahedron'],e['permutation']; b=permutations[u]
                result[order[t]][a[f]]={'tetrahedron':order[u], 'permutation':[b[p[inv[v]]] for v in range(4)]}
    return result
