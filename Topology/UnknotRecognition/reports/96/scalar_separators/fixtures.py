"""Reproducible algebraic models and two explicitly sourced normal fixtures."""
from fractions import Fraction as F
from .model import Node,Model


def gain_chain(m, threshold=None, gains=(2,3)):
    """m binary choices, one scalar seam per adjacency, 2**m source rays.

    Leaf variable start is t0; root variable end is tm. Each stage has local
    alternatives u,v. Ports transmit t_i. Equality t_next=a*u+b*v is assigned
    to the stage and paired through a scalar port; no normal-surface claim.
    """
    if m<1:
        raise ValueError('m must be positive')
    a,b=gains
    nodes=[]
    # Node 0 is terminal. Nodes 1..m are stages in reverse temporal order.
    nodes.append(Node(('end',),(1,),((1,-1),)))
    for v in range(1,m+1):
        names=(f'u{v}',f'v{v}')
        ports=(v,v+1)
        nodes.append(Node(names,ports,((-a,-b,1,0),(-1,-1,0,1)),((0,1),)))
    nodes.append(Node(('start',),(m+1,),((1,-1),)))
    parent=(-1,)+tuple(range(m+1))
    if threshold is None:
        threshold=max(a,b)**m
    return Model(parent,tuple(nodes)).validate(), {'end':F(1),'start':F(-threshold)}


def scalar_star():
    # Both signs are attainable on leaf edge 1 and 2; root links their fluxes.
    return Model((-1,0,0),(
        Node((),(1,2),((1,1),)),
        Node(('a','b'),(1,),((1,-1,-1),),((0,1),)),
        Node(('c','d'),(2,),((1,-1,-1),),((0,1),)),
    )).validate()


def solid_torus():
    """Exact face-pairing fixture from ProveIt test_normal_sector_integration.py."""
    return {'tetrahedra': [[
        {'tetrahedron':0,'permutation':[1,2,3,0]},
        {'tetrahedron':0,'permutation':[3,0,1,2]},None,None]]}


def capped_solid_torus():
    t=solid_torus()
    t['tetrahedra'][0][2]={'tetrahedron':1,'permutation':[0,1,3,2]}
    t['tetrahedra'].append([None,None,None,{'tetrahedron':0,'permutation':[0,1,3,2]}])
    return t


def normal_matching(tri):
    """Build standard face-matching equations, NOT a manifold/source validator.

    Reciprocal face gluings are validated, but vertex links and knot-exterior
    ancestry are not. The two bundled examples have repository provenance.
    """
    ts=tri['tetrahedra']; n=len(ts)
    pairs=((1,0,3,2),(2,3,0,1),(3,2,1,0))
    rows=[]
    for t,faces in enumerate(ts):
        if len(faces)!=4:
            raise ValueError('tetrahedron must have four faces')
        for f,g in enumerate(faces):
            if g is None:
                continue
            s=g['tetrahedron']; p=g['permutation']
            if not 0<=s<n or sorted(p)!=list(range(4)):
                raise ValueError('invalid face gluing')
            h=p[f]; reverse=ts[s][h]
            if reverse is None or reverse['tetrahedron']!=t or any(reverse['permutation'][p[i]]!=i for i in range(4)):
                raise ValueError('nonreciprocal face gluing')
            if (s,h)<(t,f):
                continue
            for v in range(4):
                if v==f:
                    continue
                q=next(i for i,pp in enumerate(pairs) if pp[f]==v)
                qq=next(i for i,pp in enumerate(pairs) if pp[h]==p[v])
                row=[0]*(7*n)
                row[7*t+v]+=1; row[7*t+4+q]+=1
                row[7*s+p[v]]-=1; row[7*s+4+qq]-=1
                rows.append(tuple(row))
    conflicts=tuple((7*t+4+i,7*t+4+j) for t in range(n) for i in range(3) for j in range(i+1,3))
    return tuple(rows),7*n,conflicts


def normal_euler(tri):
    """Rational V-E+F coefficients, with source-edge equivalence classes.

    Like normal_matching, this is a small fixture adapter, not a topological
    validator. Interior normal arcs count one half per local occurrence;
    boundary arcs count one; edge points count reciprocal edge degree.
    """
    from itertools import combinations
    normal_matching(tri)  # reciprocity validation
    ts=tri['tetrahedra']; local=list(combinations(range(4),2))
    ids={(t,e):6*t+j for t in range(len(ts)) for j,e in enumerate(local)}
    parent=list(range(6*len(ts)))
    def root(a):
        while parent[a]!=a:
            parent[a]=parent[parent[a]]; a=parent[a]
        return a
    def union(a,b):
        a=root(a);b=root(b)
        if a!=b:parent[a]=b
    for t,faces in enumerate(ts):
        for f,g in enumerate(faces):
            if g is None:continue
            p=g['permutation'];s=g['tetrahedron']
            for edge in local:
                if f not in edge:
                    image=tuple(sorted(p[v] for v in edge))
                    union(ids[t,edge],ids[s,image])
    degree={}
    for j in range(len(parent)):
        r=root(j);degree[r]=degree.get(r,0)+1
    opposite=(((0,1),(2,3)),((0,2),(1,3)),((0,3),(1,2)))
    coeff=[]
    for t,faces in enumerate(ts):
        for typ in range(7):
            if typ<4:
                edges=[e for e in local if typ in e]
                hitfaces=[f for f in range(4) if f!=typ]
            else:
                edges=[e for e in local if e not in opposite[typ-4]]
                hitfaces=list(range(4))
            c=F(1)-sum((F(1,2) if faces[f] is not None else F(1)) for f in hitfaces)
            c+=sum(F(1,degree[root(ids[t,e])]) for e in edges)
            coeff.append(c)
    return tuple(coeff)
