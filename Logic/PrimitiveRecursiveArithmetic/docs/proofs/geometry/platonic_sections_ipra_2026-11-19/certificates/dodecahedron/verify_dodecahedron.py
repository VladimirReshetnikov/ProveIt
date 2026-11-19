#!/usr/bin/env python3
"""Exact finite dodecahedron section certificate verifier (Python stdlib only).

No floating point, symbolic package, optimization routine, or trusted geometry
library is used. The mathematical reduction is explained in dodecahedron_proof.tex.
Coefficients are in Q(phi), where phi^2=phi+1 and 1<phi<2.
"""
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path
import json
import sys

ZERO = (F(0), F(0))
ONE = (F(1), F(0))
PHI = (F(0), F(1))
LO, HI = F(161803, 100000), F(161804, 100000)

def q(a=0, b=0): return (F(a), F(b))
def add(a,b): return (a[0]+b[0], a[1]+b[1])
def neg(a): return (-a[0],-a[1])
def sub(a,b): return add(a,neg(b))
def mul(a,b):
    return (a[0]*b[0]+a[1]*b[1], a[0]*b[1]+a[1]*b[0]+a[1]*b[1])
def inv(a):
    d=a[0]*a[0]+a[0]*a[1]-a[1]*a[1]
    assert d
    return ((a[0]+a[1])/d, -a[1]/d)
def div(a,b): return mul(a,inv(b))
def qsum(xs):
    out=ZERO
    for x in xs: out=add(out,x)
    return out

def sign(a):
    """Exact sign by comparing rational squares; valid since sqrt(5)>0."""
    A,B=2*a[0]+a[1],a[1] # 2a = A+B sqrt(5)
    if not B: return (A>0)-(A<0)
    if not A: return (B>0)-(B<0)
    if A>0 and B>0: return 1
    if A<0 and B<0: return -1
    d=A*A-5*B*B
    return ((d>0)-(d<0)) if A>0 else ((d<0)-(d>0))

def lower(a): return a[0]+a[1]*(LO if a[1]>=0 else HI)
def vecadd(a,b): return tuple(add(x,y) for x,y in zip(a,b))
def vscale(t,a): return tuple(mul(t,x) for x in a)
def dot(a,b): return qsum(mul(x,y) for x,y in zip(a,b))
def vcross(a,b):
    return (sub(mul(a[1],b[2]),mul(a[2],b[1])),sub(mul(a[2],b[0]),mul(a[0],b[2])),sub(mul(a[0],b[1]),mul(a[1],b[0])))
def mv(A,v): return tuple(dot(row,v) for row in A)
def mm(A,B): return tuple(tuple(qsum(mul(A[i][k],B[k][j]) for k in range(3)) for j in range(3)) for i in range(3))
def transpose(A): return tuple(tuple(A[j][i] for j in range(3)) for i in range(3))
I=tuple(tuple(ONE if i==j else ZERO for j in range(3)) for i in range(3))

def clean(P): return {m:c for m,c in P.items() if c!=ZERO}
def const(c): return {} if c==ZERO else {(0,0,0):c}
def variable(i):
    m=[0,0,0];m[i]=1
    return {tuple(m):ONE}
def padd(P,Q):
    R=P.copy()
    for m,c in Q.items(): R[m]=add(R.get(m,ZERO),c)
    return clean(R)
def pscale(c,P): return clean({m:mul(c,a) for m,a in P.items()})
def psub(P,Q): return padd(P,pscale(q(-1),Q))
def pmul(P,Q):
    R={}
    for a,c in P.items():
        for b,d in Q.items():
            m=tuple(x+y for x,y in zip(a,b))
            R[m]=add(R.get(m,ZERO),mul(c,d))
    return clean(R)
def ppow(P,n):
    R=const(ONE)
    for _ in range(n): R=pmul(R,P)
    return R
def pprod(Ps):
    R=const(ONE)
    for P in Ps: R=pmul(R,P)
    return R
def psum(Ps):
    R={}
    for P in Ps: R=padd(R,P)
    return R
def subst(P,forms):
    maxdeg=[max((m[i] for m in P), default=0) for i in range(3)]
    powers=[[ppow(forms[i],k) for k in range(maxdeg[i]+1)] for i in range(3)]
    return psum(pscale(c,pprod(powers[i][m[i]] for i in range(3))) for m,c in P.items())
def peval(P,point):
    return qsum(mul(c,qprod(qpow(point[i],m[i]) for i in range(3))) for m,c in P.items())
def qpow(a,k):
    r=ONE
    for _ in range(k): r=mul(r,a)
    return r
def qprod(xs):
    r=ONE
    for x in xs:r=mul(r,x)
    return r

def parseq(a): return tuple(F(t) for t in a)
def parsep(P):
    assert len({tuple(m) for m,c in P})==len(P)
    return clean({tuple(m):parseq(c) for m,c in P})
def linear(v): return psum(pscale(c,variable(i)) for i,c in enumerate(v))

def verify(path):
    data=json.loads(path.read_text())
    assert LO>1 and LO*LO-LO-1<0 and HI*HI-HI-1>0
    vertices=[tuple(parseq(c) for c in v) for v in data['vertices']]
    rays={k:tuple(parseq(c) for c in v) for k,v in data['rays'].items()}
    p1=sub(PHI,ONE)
    expected_vertices=[tuple(q(c) for c in v) for v in product([-1,1],repeat=3)]
    expected_vertices += [(ZERO,mul(q(a),p1),mul(q(b),PHI)) for a,b in product([-1,1],repeat=2)]
    expected_vertices += [(mul(q(a),p1),mul(q(b),PHI),ZERO) for a,b in product([-1,1],repeat=2)]
    expected_vertices += [(mul(q(a),PHI),ZERO,mul(q(b),p1)) for a,b in product([-1,1],repeat=2)]
    assert vertices==expected_vertices
    assert rays['F']==(ZERO,PHI,ONE)
    assert rays['E']==(ONE,PHI,add(PHI,ONE))
    assert rays['V']==(ONE,ONE,ONE)
    assert rays['T']==vecadd(vscale(q(2),rays['F']),vscale(p1,rays['E']))
    assert rays['S']==vecadd(rays['F'],vscale(p1,rays['V']))
    assert parseq(data['max_area_squared'])==q(F(75,4),25)
    edge_sq=mul(q(4),qpow(p1,2))
    edges={tuple((i,j)) for i,j in combinations(range(20),2) if dot(vecadd(vertices[i],vscale(q(-1),vertices[j])),vecadd(vertices[i],vscale(q(-1),vertices[j])))==edge_sq}
    assert len(edges)==30
    # Facet normals. Their common support constant is phi^2.
    normals=[]
    for a,b in product([-1,1],repeat=2):
        normals.extend([(ZERO,mul(q(a),PHI),q(b)),(q(b),ZERO,mul(q(a),PHI)),(mul(q(a),PHI),q(b),ZERO)])
    support=add(PHI,ONE)
    facets=[]
    for n in normals:
        assert all(sign(sub(support,dot(n,v)))>=0 for v in vertices)
        face={i for i,v in enumerate(vertices) if dot(n,v)==support}
        assert len(face)==5
        assert sum(1 for i,j in edges if i in face and j in face)==5
        facets.append(face)
    # Enumerate all possible supporting facet planes to check completeness.
    recovered_facets=set()
    for i,j,k in combinations(range(20),3):
        a=vecadd(vertices[j],vscale(q(-1),vertices[i]))
        b=vecadd(vertices[k],vscale(q(-1),vertices[i]))
        normal=vcross(a,b)
        if normal==(ZERO,ZERO,ZERO): continue
        offset=dot(normal,vertices[i])
        side=[sign(sub(dot(normal,v),offset)) for v in vertices]
        if all(t>=0 for t in side) or all(t<=0 for t in side):
            recovered_facets.add(frozenset(h for h,t in enumerate(side) if t==0))
    assert recovered_facets==set(map(frozenset,facets))
    facet_edges={tuple(sorted(a&b)) for a,b in combinations(facets,2) if len(a&b)==2}
    assert facet_edges==edges
    # Reflection group and the chamber argument use only this finite closure.
    wall_normals=[(q(-1),PHI,sub(ONE,PHI)),(sub(ONE,PHI),q(-1),PHI),(add(PHI,ONE),ONE,neg(PHI))]
    basis=[rays[k] for k in ['F','E','V']]
    reflections=[]
    for i,a in enumerate(wall_normals):
        assert sign(dot(a,basis[i]))>0
        assert all(dot(a,basis[j])==ZERO for j in range(3) if i!=j)
        R=tuple(tuple(sub(I[j][k],div(mul(q(2),mul(a[j],a[k])),dot(a,a))) for k in range(3)) for j in range(3))
        assert mm(transpose(R),R)==I
        assert {mv(R,v) for v in vertices}==set(vertices)
        reflections.append(R)
    group=[I];seen={I}
    for A in group:
        for B in reflections:
            C=mm(A,B)
            if C not in seen:
                seen.add(C);group.append(C)
                assert len(group)<=120
    assert len(group)==120
    print('Geometry: 20 vertices, 30 edges, 12 pentagonal facets; 120 symmetries.')
    X,Y,Z=[variable(i) for i in range(3)]
    cells_expected=[['F','T','S'],['T','E','S'],['E','V','S']]
    for ci,cell in enumerate(data['cells']):
        assert cell['rays']==cells_expected[ci]
        cone=[rays[k] for k in cell['rays']]
        representative=tuple(qsum(v[i] for v in cone) for i in range(3))
        signs=[sign(dot(representative,v)) for v in vertices]
        assert all(signs)
        cycle=[tuple(e) for e in cell['edge_cycle']]
        assert len(set(tuple(sorted(e)) for e in cycle))==len(cycle)
        assert set(tuple(sorted(e)) for e in cycle)=={e for e in edges if signs[e[0]]*signs[e[1]]<0}
        for i,v in enumerate(vertices):
            assert all(sign(dot(r,v))*signs[i]>=0 for r in cone)
        for a,b in zip(cycle,cycle[1:]+cycle[:1]):
            assert sum(1 for face in facets if set(a+b)<=face)==1
        denoms=[];numerators=[]
        for i,j in cycle:
            di,dj=linear(vertices[i]),linear(vertices[j])
            denoms.append(psub(di,dj))
            numerators.append([psub(pscale(vertices[j][k],di),pscale(vertices[i][k],dj)) for k in range(3)])
            # Every used edge has a nonzero denominator at every cone ray,
            # except the E ray in the middle cone, handled by the final cone.
            for ki,r in enumerate(cone):
                val=dot(r,vecadd(vertices[i],vscale(q(-1),vertices[j])))
                assert val!=ZERO or (ci==1 and ki==1)
        L=pprod(denoms)
        shoelace={}
        m=len(cycle)
        for k in range(m):
            h=(k+1)%m
            cross=psub(pmul(numerators[k][0],numerators[h][1]),pmul(numerators[k][1],numerators[h][0]))
            shoelace=padd(shoelace,pmul(cross,pprod(denoms[j] for j in range(m) if j!=k and j!=h)))
        N,D=parsep(cell['numerator_xyz']),parsep(cell['denominator_xyz'])
        assert psub(pscale(q(2),pprod([Z,N,L])),pmul(D,shoelace))=={}, ('area identity',ci)
        forms=[linear([r[i] for r in cone]) for i in range(3)]
        Ns,Ds=subst(N,forms),subst(D,forms)
        normsq=psum(pmul(n,n) for n in forms)
        H=psub(pscale(q(75,100),pmul(Ds,Ds)),pscale(q(4),pmul(normsq,pmul(Ns,Ns))))
        assert H==parsep(cell['bound_polynomial_uvw']),('bound identity',ci)
        assert len(H)==cell['coefficient_count']
        assert all(sum(m)==cell['degree'] for m in H)
        bounds=[lower(c) for c in H.values()]
        assert min(bounds)==F(cell['minimum_coefficient_lower_bound'])>0
        # All denominator coefficients are nonnegative, and pure powers
        # ensure positivity away from zero (or away from E in cone 1).
        assert all(sign(c)>0 for c in Ds.values())
        degree=max(sum(m) for m in Ds)
        for k in ([0,2] if ci==1 else [0,1,2]):
            m=[0,0,0];m[k]=degree
            assert sign(Ds.get(tuple(m),ZERO))>0
        print(f'Cell {ci}: shoelace identity exact; degree {cell["degree"]}, {len(H)} positive coefficients; lower bound {min(bounds)}.')
    assert len(data['cells'])==3
    print('PASS: every central section has area squared <= 25*(4*phi+3)/4.')
    print('The finite convexity lemma in the report transfers this bound to every affine section.')

if __name__=='__main__':
    verify(Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).with_name('dodecahedron_certificate.json'))
