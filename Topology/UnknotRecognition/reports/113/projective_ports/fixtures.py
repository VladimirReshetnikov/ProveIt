"""Small reproducible fixtures. Face pairings adapted from ProveIt report 96.

Source path: reports/96/scalar_separators/fixtures.py at repository revision
74de08949619863b002b5fcf01813a2faddde212. These are mathematical fixtures,
not knot-diagram-authenticated exteriors. See SOURCE_AUDIT.md.
"""
from fractions import Fraction as F
from itertools import combinations
from .model import Block
from .source import Source


def sleeve_blocks(m):
    if type(m) is not int or m<1: raise ValueError('positive number of blocks required')
    block=Block(4,(),((3,1,2,0),(0,2,1,3)),((0,2),(0,3),(1,2),(1,3)))
    return (block,)*m


def sleeve_costs(m):
    return tuple(tuple(((i+2)*(j+3)*7+3*j)%19-9 for j in range(4)) for i in range(m))


def centroid_blocks():
    return (Block(2,(),((2,0),(0,1),(0,1))),
            Block(2,(),((0,1),(2,0),(0,1))))


def false_convexification():
    return (Block(2,(),((1,0),(0,1)),((0,1),)),
            Block(1,(),((1,),(1,))))


def solid_torus():
    return {'tetrahedra': [[
        {'tetrahedron':0,'permutation':[1,2,3,0]},
        {'tetrahedron':0,'permutation':[3,0,1,2]},None,None]]}


def capped_solid_torus():
    t=solid_torus()
    t['tetrahedra'][0][2]={'tetrahedron':1,'permutation':[0,1,3,2]}
    t['tetrahedra'].append([None,None,None,{'tetrahedron':0,'permutation':[0,1,3,2]}])
    return t


def matching(tri):
    ts=tri['tetrahedra']; n=len(ts)
    pairs=((1,0,3,2),(2,3,0,1),(3,2,1,0));rows=[]
    for t,faces in enumerate(ts):
        if len(faces)!=4:raise ValueError('four faces required')
        for f,g in enumerate(faces):
            if g is None:continue
            s=g['tetrahedron'];p=g['permutation']
            if type(s) is not int or not 0<=s<n or sorted(p)!=list(range(4)):
                raise ValueError('invalid gluing')
            h=p[f];back=ts[s][h]
            if back is None or back['tetrahedron']!=t or any(back['permutation'][p[j]]!=j for j in range(4)):
                raise ValueError('nonreciprocal gluing')
            if (s,h)<(t,f):continue
            for v in range(4):
                if v==f:continue
                q=next(j for j,pp in enumerate(pairs) if pp[f]==v)
                qq=next(j for j,pp in enumerate(pairs) if pp[h]==p[v])
                row=[0]*(7*n)
                row[7*t+v]+=1;row[7*t+4+q]+=1
                row[7*s+p[v]]-=1;row[7*s+4+qq]-=1;rows.append(tuple(row))
    conflicts=tuple((7*t+4+i,7*t+4+j) for t in range(n) for i in range(3) for j in range(i+1,3))
    return Source(7*n,tuple(rows),conflicts)


def euler(tri):
    matching(tri)
    ts=tri['tetrahedra'];edges=list(combinations(range(4),2))
    ids={(t,e):6*t+j for t in range(len(ts)) for j,e in enumerate(edges)}
    parent=list(range(6*len(ts)))
    def root(a):
        while parent[a]!=a:
            parent[a]=parent[parent[a]];a=parent[a]
        return a
    for t,faces in enumerate(ts):
        for f,g in enumerate(faces):
            if g is None:continue
            p=g['permutation'];s=g['tetrahedron']
            for edge in edges:
                if f not in edge:
                    image=tuple(sorted(p[v] for v in edge))
                    a,b=root(ids[t,edge]),root(ids[s,image]);parent[a]=b
    degree={}
    for j in range(len(parent)):degree[root(j)]=degree.get(root(j),0)+1
    opposite=(((0,1),(2,3)),((0,2),(1,3)),((0,3),(1,2)))
    coeff=[]
    for t,faces in enumerate(ts):
        for typ in range(7):
            if typ<4:
                hit=[e for e in edges if typ in e]; ff=[f for f in range(4) if f!=typ]
            else:
                hit=[e for e in edges if e not in opposite[typ-4]];ff=range(4)
            v=F(1)-sum((F(1,2) if faces[f] is not None else F(1)) for f in ff)
            v+=sum(F(1,degree[root(ids[t,e])]) for e in hit)
            coeff.append(v)
    return tuple(coeff)


def nonextreme_assembly(q=3):
    """A two-port atlas mixture need not be a source extreme ray."""
    if type(q) is not int or q<=1:raise ValueError('q must exceed one')
    return (Block(4,((1,1,-1,-1),),((1,0,1,0),(0,1,0,1))),
            Block(1,(),((1,),(q,))))
