"""Objective-independent projective atlases, with exact compatible mixtures."""
from dataclasses import dataclass
from itertools import combinations
from .exact import Q, dot, matrix, rational, nullspace, primitive, solve_unique
from .model import enumerate_rays, enumerate_rays_by_zeros, ResourceLimit


@dataclass(frozen=True)
class Ray:
    source: tuple
    support: frozenset
    port: tuple
    vector: tuple


@dataclass(frozen=True)
class Simplex:
    rays: tuple
    support: frozenset


def projective_atlas(point_sets, d, *, max_candidates=None, check=lambda:None):
    """Two ports: ray images only. Higher ports: arrangement vertices.

    Hyperplanes are built locally, then deduplicated globally. The coordinate
    frame captures simplex faces of every dimension, including isolated points.
    """
    if d==1:
        return ((Q(1),),), {'hyperplanes':0,'candidate_systems':1}
    if d==2:
        pts=tuple(sorted(set(p for ps in point_sets for p in ps)))
        return pts, {'hyperplanes':len(pts),'candidate_systems':len(pts)}
    frame=tuple(tuple(Q(i==j) for i in range(d)) for j in range(d))
    hyper=set()
    for points in point_sets:
        local=tuple(sorted(set(points)|set(frame)))
        for subset in combinations(local,d-1):
            check()
            z=nullspace(subset,d)
            if len(z)==1:
                hyper.add(primitive(z[0],True))
    vertices=set(); tried=0
    for subset in combinations(sorted(hyper),d-1):
        check(); tried+=1
        if max_candidates is not None and tried>max_candidates:
            raise ResourceLimit('atlas intersection budget exhausted')
        y=solve_unique(tuple(subset)+(tuple(Q(1) for _ in range(d)),),
                       (Q(0),)*(d-1)+(Q(1),), d)
        if y is not None and all(v>=0 for v in y):
            vertices.add(y)
    return tuple(sorted(vertices)), {'hyperplanes':len(hyper),'candidate_systems':tried}


class Prepared:
    """Reusable complete atlas. Construction never depends on query objectives.

    Rational input must be int/Fraction/string. A resource cap raises
    ResourceLimit; no incomplete computation returns NO_POSITIVE.
    """
    def __init__(self, blocks, *, max_supports=None, max_candidates=None,
                 check=lambda:None, ray_method="support"):
        self.blocks=tuple(blocks)
        if not self.blocks or len({b.d for b in self.blocks})!=1:
            raise ValueError('nonempty blocks must have identical port dimension')
        self.d=self.blocks[0].d
        if ray_method not in ('support','zeros'):
            raise ValueError('ray_method must be support or zeros')
        enumerator=enumerate_rays if ray_method=='support' else enumerate_rays_by_zeros
        self.raw_rays=tuple(enumerator(b,max_supports=max_supports,check=check)
                            for b in self.blocks)
        zero=[]; rays=[]; simplices=[]
        for b,raw in zip(self.blocks,self.raw_rays):
            zr=[]; rr=[]
            for r in raw:
                image=b.image(r); h=sum(image,Q(0)); support=frozenset(j for j,v in enumerate(r) if v)
                if not h:
                    zr.append(r)
                else:
                    rr.append(Ray(r,support,tuple(v/h for v in image),tuple(Q(v)/h for v in r)))
            ss=[]
            for k in range(1,min(self.d,len(rr))+1):
                for ids in combinations(range(len(rr)),k):
                    check()
                    support=frozenset().union(*(rr[j].support for j in ids))
                    if not b.compatible_support(support): continue
                    cols=tuple(tuple(rr[j].port[h] for j in ids) for h in range(self.d))
                    # Independence of normalized port columns is affine independence.
                    if nullspace(cols,k): continue
                    ss.append(Simplex(ids,support))
            zero.append(tuple(zr)); rays.append(tuple(rr)); simplices.append(tuple(ss))
        self.zero_rays=tuple(zero); self.rays=tuple(rays); self.simplices=tuple(simplices)
        self.vertices,self.stats=projective_atlas(
            [tuple(r.port for r in rr) for rr in self.rays],self.d,
            max_candidates=max_candidates,check=check)
        self.stats=dict(self.stats, rays=sum(map(len,self.raw_rays)),
                        nonzero_port_rays=sum(map(len,self.rays)),
                        simplices=sum(map(len,self.simplices)), vertices=len(self.vertices))
        # Store all feasible barycentric mixtures at atlas vertices. This cache
        # is independent of objectives and zero-face restrictions.
        tables=[]
        for rr,ss in zip(self.rays,self.simplices):
            table=[]
            for y in self.vertices:
                choices=[]
                for simplex in ss:
                    check()
                    cols=tuple(tuple(rr[j].port[h] for j in simplex.rays) for h in range(self.d))
                    w=solve_unique(cols,y,len(simplex.rays))
                    if w is not None and all(a>=0 for a in w):
                        # Zero coefficients must not exclude a valid anchor.
                        actual=frozenset().union(*(rr[j].support for j,a in zip(simplex.rays,w) if a))
                        choices.append((simplex.rays,w,actual))
                table.append(tuple(choices))
            tables.append(tuple(table))
        self.tables=tuple(tables)

    def solve(self, objectives, *, master=None, zeros=None, check=lambda:None):
        costs=tuple(tuple(rational(v) for v in c) for c in objectives)
        if len(costs)!=len(self.blocks) or any(len(c)!=b.n for c,b in zip(costs,self.blocks)):
            raise ValueError('objective dimensions do not match blocks')
        c0=(Q(0),)*self.d if master is None else tuple(rational(v) for v in master)
        if len(c0)!=self.d: raise ValueError('master objective dimension mismatch')
        zz=tuple(frozenset(z) for z in zeros) if zeros is not None else tuple(frozenset() for _ in self.blocks)
        if len(zz)!=len(self.blocks) or any(any(type(j) is not int or j<0 or j>=b.n for j in z) for b,z in zip(self.blocks,zz)):
            raise ValueError('invalid zero restrictions')
        for i,(b,zr,c,z) in enumerate(zip(self.blocks,self.zero_rays,costs,zz)):
            for r in zr:
                check()
                if any(r[j] for j in z): continue
                value=dot(c,r)
                if value>0:
                    vectors=[(Q(0),)*bb.n for bb in self.blocks]; vectors[i]=tuple(map(Q,r))
                    return {'status':'POSITIVE','kind':'zero-port','port':(Q(0),)*self.d,
                            'value':value,'vectors':tuple(vectors),'vertex_index':None}
        reward=tuple(tuple(dot(c,r.vector) for r in rr) for c,rr in zip(costs,self.rays))
        best=None
        for t,y in enumerate(self.vertices):
            check(); value=dot(c0,y); chosen=[]
            for i in range(len(self.blocks)):
                optimum=None
                for ids,weights,support in self.tables[i][t]:
                    check()
                    if support & zz[i]: continue
                    score=sum((a*reward[i][j] for j,a in zip(ids,weights)),Q(0))
                    if optimum is None or score>optimum[0]: optimum=(score,ids,weights)
                if optimum is None: break
                value+=optimum[0]; chosen.append(optimum)
            if len(chosen)!=len(self.blocks): continue
            if best is None or value>best[0]: best=(value,t,chosen)
        if best is None:
            return {'status':'NO_POSITIVE','kind':'no-common-nonzero-port','value':None,
                    'port':None,'vectors':None,'vertex_index':None}
        value,t,chosen=best
        vectors=[]
        for b,rr,(_,ids,w) in zip(self.blocks,self.rays,chosen):
            vectors.append(tuple(sum((a*rr[j].vector[h] for j,a in zip(ids,w)),Q(0)) for h in range(b.n)))
        return {'status':'POSITIVE' if value>0 else 'NO_POSITIVE', 'kind':'atlas',
                'value':value,'port':self.vertices[t],'vectors':tuple(vectors),'vertex_index':t}
