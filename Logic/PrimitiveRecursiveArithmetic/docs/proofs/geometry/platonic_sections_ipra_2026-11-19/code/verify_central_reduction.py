#!/usr/bin/env python3
"""Executable finite trapezoid construction for the central-section lemma.
Uses exact_sections.py beside this script. Standard library; exact Q(phi).
This is an arithmetic reference implementation, not a completed Lean proof.
"""
from fractions import Fraction as F
from exact_sections import G, P, solids, edges, section, area2, hull2, supporting_faces, dot, cross, sub, scale

def fiber(poly,x):
    values=[q[1] for q in poly if q[0]==x]
    for q,r in zip(poly,poly[1:]+poly[:1]):
        if min(q[0],r[0])<x<max(q[0],r[0]):
            values.append(q[1]+(x-q[0])*(r[1]-q[1])/(r[0]-q[0]))
    assert values
    return min(values),max(values)

def equal_area_central_polygon(Q,n):
    """Returns a coplanar central polygon W with area(W)=area(Q).
    If Q⊂K and K=-K is convex, W⊂K by the endpoint half-difference formula.
    """
    n=tuple(G.of(x) for x in n)
    j=next(i for i,x in enumerate(n) if x.sign())
    axes=[i for i in range(3) if i!=j]
    if len(Q)<3:return [],[]
    S=[(q[axes[0]],q[axes[1]]) for q in Q]
    a=min(q[0] for q in S);b=max(q[0] for q in S)
    if a==b:return [],[]
    middle=(a+b)/2
    B=sorted({q[0] for q in S}|{a+b-q[0] for q in S})
    assert len(B)<=2*len(Q)
    fs=[];lower=[];upper=[]
    for x in B:
        l,u=fiber(S,x);lr,ur=fiber(S,a+b-x)
        lower.append((x-middle,(l-ur)/2))
        upper.append((x-middle,(u-lr)/2))
        fs.append(u-l)
    planar=hull2([(x,y,(x,y)) for x,y in lower+upper])
    W=[]
    for x,y,_ in planar:
        v=[G(0)]*3;v[axes[0]],v[axes[1]]=x,y
        v[j]=-sum((n[k]*v[k] for k in axes),G(0))/n[j]
        W.append(tuple(v))
    T=[];U=[];r=len(B)-1
    for i in range(r):
        delta=B[i+1]-B[i]
        assert delta==B[r-i]-B[r-i-1]
        T.append(delta*(fs[i]+fs[i+1])/2)
        U.append(delta*(fs[i]+fs[i+1]+fs[r-i]+fs[r-i-1])/4)
    for i in range(r):assert 2*U[i]==T[i]+T[r-i-1]
    assert sum(T,G(0))==sum(U,G(0))
    assert area2(W)==area2(Q)
    return W,[(t.data(),u.data()) for t,u in zip(T,U)]

def inside(V,FACES,p):
    for face in FACES:
        a,b,c=(V[i] for i in face[:3])
        n=cross(sub(b,a),sub(c,a));d=dot(n,a)
        if d<0:n,d=scale(-1,n),-d
        assert d>0
        if dot(n,p)>d:return False
    return True

def audit():
    all_solids=solids();count=0
    for name in ['cube','octahedron','dodecahedron','icosahedron']:
        V=all_solids[name]; E=edges(V);FACES=supporting_faces(V)
        for n,t in [((1,2,3),G(F(1,3))),((2,-3,1),G(F(3,7)))]:
            Q=section(V,n,t,E);Q0=section(V,n,G(0),E)
            W,_=equal_area_central_polygon(Q,n)
            assert area2(W)==area2(Q)<=area2(Q0)
            assert all(dot(tuple(map(G.of,n)),p)==G(0) and inside(V,FACES,p) for p in W)
            count+=1
    V=all_solids['cube']; E=edges(V);FACES=supporting_faces(V)
    for n,t in [((1,0,0),G(1)),((1,1,0),G(2)),((1,1,1),G(3)),((1,2,3),G(100))]:
        Q=section(V,n,t,E);W,_=equal_area_central_polygon(Q,n)
        assert area2(W)==area2(Q)
        assert all(inside(V,FACES,p) for p in W)
        count+=1
    print(f'PASS: {count} exact central-polygon constructions, including a supporting face, edge, point, and empty section.')
    print('Every positive-area instance checks all trapezoid equalities and containment in the central section.')

if __name__=='__main__':audit()
