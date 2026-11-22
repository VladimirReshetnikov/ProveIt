#!/usr/bin/env python3
"""Exact certificate for all central sections of the regular icosahedron.
Python standard library only. All calculations occur in Q(sqrt(5)).
Run from any directory; certificate0.json and certificate1.json must be beside
this script. No numerical optimization or floating-point arithmetic is used.
"""
from fractions import Fraction as F
from itertools import product, combinations
from pathlib import Path
import json

class K:
    __slots__=('a','b')
    def __init__(self,a=0,b=0):
        if isinstance(a,K): self.a,self.b=a.a,a.b
        else: self.a,self.b=F(a),F(b)
    def __add__(self,o):
        o=K(o);return K(self.a+o.a,self.b+o.b)
    __radd__=__add__
    def __neg__(self):return K(-self.a,-self.b)
    def __sub__(self,o):return self+-K(o)
    def __rsub__(self,o):return K(o)+-self
    def __mul__(self,o):
        o=K(o);return K(self.a*o.a+5*self.b*o.b,self.a*o.b+self.b*o.a)
    __rmul__=__mul__
    def inv(self):
        d=self.a*self.a-5*self.b*self.b
        assert d
        return K(self.a/d,-self.b/d)
    def __truediv__(self,o):return self*K(o).inv()
    def __rtruediv__(self,o):return K(o)*self.inv()
    def __pow__(self,n):
        if n<0:return self.inv()**(-n)
        r=K(1)
        for _ in range(n):r=r*self
        return r
    def __eq__(self,o):
        o=K(o);return self.a==o.a and self.b==o.b
    def __hash__(self):return hash((self.a,self.b))
    def __bool__(self):return bool(self.a or self.b)
    def sign(self):
        if not self.a:return (self.b>0)-(self.b<0)
        if not self.b:return (self.a>0)-(self.a<0)
        if self.a>0 and self.b>0:return 1
        if self.a<0 and self.b<0:return -1
        d=self.a*self.a-5*self.b*self.b
        return ((d>0)-(d<0))*((self.a>0)-(self.a<0))
    def pair(self):return [str(self.a),str(self.b)]
    def __repr__(self):return f'({self.a})+({self.b})sqrt(5)'

ZERO=(0,0,0)
def clean(p):return {m:v for m,v in p.items() if v}
def const(v):return {ZERO:K(v)} if v else {}
def linear(v):return clean({tuple(int(i==j) for i in range(3)):K(v[j]) for j in range(3)})
def add(p,q):
    r=p.copy()
    for m,v in q.items():r[m]=r.get(m,K())+v
    return clean(r)
def neg(p):return {m:-v for m,v in p.items()}
def sub(p,q):return add(p,neg(q))
def scale(p,c):return clean({m:v*c for m,v in p.items()})
def mul(p,q):
    r={}
    for m,u in p.items():
        for n,v in q.items():
            t=tuple(m[i]+n[i] for i in range(3))
            r[t]=r.get(t,K())+u*v
    return clean(r)
def power(p,n):
    r=const(1)
    for _ in range(n):r=mul(r,p)
    return r
def prod(ps):
    r=const(1)
    for p in ps:r=mul(r,p)
    return r
def compose(p,vs):
    d=max((max(m) for m in p),default=0)
    powers=[[power(linear(v),i) for i in range(d+1)] for v in vs]
    r={}
    for m,c in p.items():r=add(r,scale(prod(powers[i][m[i]] for i in range(3)),c))
    return r
def evaluate(p,v):return sum((c*prod_k(v[i]**m[i] for i in range(3)) for m,c in p.items()),K())
def prod_k(vs):
    r=K(1)
    for v in vs:r=r*v
    return r
def dot(u,v):return sum((a*b for a,b in zip(u,v)),K())
def vecadd(u,v):return tuple(a+b for a,b in zip(u,v))
def vecsub(u,v):return tuple(a-b for a,b in zip(u,v))
def vmul(c,v):return tuple(c*a for a in v)
def cross(u,v):return (u[1]*v[2]-u[2]*v[1],u[2]*v[0]-u[0]*v[2],u[0]*v[1]-u[1]*v[0])
def loadpoly(ts):return {tuple(m):K(a,b) for m,a,b in ts}

phi=K(F(1,2),F(1,2))
V=[tuple(map(K,v)) for a,b in product([-1,1],repeat=2)
   for v in [(0,a,b*phi),(a,b*phi,0),(a*phi,0,b)]]
E=[(i,j) for i in range(12) for j in range(i) if dot(vecsub(V[i],V[j]),vecsub(V[i],V[j]))==4]
assert len(V)==12 and len(set(V))==12 and len(E)==30
edges={frozenset(e) for e in E}
faces=[f for f in combinations(range(12),3) if all(frozenset(e) in edges for e in combinations(f,2))]
assert len(faces)==20
# Every triangular face is supporting; the edge incidence is closed.
for f in faces:
    q=cross(vecsub(V[f[1]],V[f[0]]),vecsub(V[f[2]],V[f[0]]))
    signs={dot(q,vecsub(v,V[f[0]])).sign() for v in V}-{0}
    assert len(signs)==1
for e in edges:assert sum(e.issubset(f) for f in faces)==2
# Independently enumerate vertices of the intersection of the 20 supporting
# halfspaces. Their antipodal normals span space, so it is bounded.
H=[]
for f in faces:
    q=cross(vecsub(V[f[1]],V[f[0]]),vecsub(V[f[2]],V[f[0]]))
    d=dot(q,V[f[0]])
    if d.sign()<0:q,d=vmul(-1,q),-d
    assert d.sign()>0 and all((dot(q,v)-d).sign()<=0 for v in V)
    H.append((q,d))
assert all((vmul(-1,q),d) in H for q,d in H)
assert any(dot(q,cross(r,s)) for (q,_),(r,_),(s,_) in combinations(H,3))
found=set()
for (q,d),(r,e),(s,f) in combinations(H,3):
    det=dot(q,cross(r,s))
    if not det:continue
    v=vmul(1/det,vecadd(vecadd(vmul(d,cross(r,s)),vmul(e,cross(s,q))),vmul(f,cross(q,r))))
    if all((dot(u,v)-g).sign()<=0 for u,g in H):found.add(v)
assert found==set(V)

# Reflection invariance proves the fundamental-cone reduction. Maximize the
# scalar product with h on the finite orbit to force its three inequalities.
m=(-phi**2,-phi,K(1))
h=(K(1),K(1),K(10))
reflection_normals=[(K(1),K(),K()),(K(),K(1),K()),m]
permutations=[]
for q in reflection_normals:
    assert dot(q,h).sign()>0
    R=[vecsub(v,vmul(2*dot(v,q)/dot(q,q),q)) for v in V]
    assert set(R)==set(V)
    permutations.append([V.index(v) for v in R])
assert dot(m,m)==4*phi**2
print('Validated 12 vertices, 30 edges, 20 supporting faces and 3 reflections.')
print('Reflection permutations:',permutations)

O=(K(),K(),K(1)); U=(K(),K(1),phi); T=(K(1),K(),phi**2); W=(phi,K(1),3*phi+1)
rays=[[O,U,W],[O,T,W]]
cycles=[[(5,1),(3,1),(7,3),(11,7),(11,8),(10,8),(10,6),(6,4),(4,2),(5,2)],
        [(5,1),(3,1),(7,1),(7,0),(8,7),(11,8),(10,8),(10,6),(10,4),(9,4),(5,4),(5,2)]]
root=Path(__file__).resolve().parent
for k in [0,1]:
    dat=json.loads((root/f'certificate{k}.json').read_text())
    N,D=loadpoly(dat['numerator']),loadpoly(dat['denominator'])
    cert=loadpoly(dat['certificate'])
    cycle=cycles[k]
    # On each open ray cone every vertex has a constant, nonzero sign.
    signs=[]
    for v in V:
        ss={dot(v,r).sign() for r in rays[k]}-{0}
        assert len(ss)==1
        signs.append(next(iter(ss)))
    crossed={frozenset(e) for e in E if signs[e[0]]!=signs[e[1]]}
    assert crossed=={frozenset(e) for e in cycle}
    assert len(crossed)==len(cycle)
    for i,e in enumerate(cycle):
        fset=set(e)|set(cycle[(i+1)%len(cycle)])
        assert any(fset.issubset(f) for f in faces)
    # Exact shoelace identity. If q_i=P_i/L_i then
    # 2*N*product L_i = D*sum det(P_i,P_(i+1))*product other L_j.
    L=[]; P=[]
    for i,j in cycle:
        ui,uj=linear(V[i]),linear(V[j])
        L.append(sub(ui,uj))
        P.append([sub(scale(ui,V[j][r]),scale(uj,V[i][r])) for r in range(3)])
    C=prod(L);S={}
    for i in range(len(cycle)):
        j=(i+1)%len(cycle)
        det=sub(mul(P[i][0],P[j][1]),mul(P[i][1],P[j][0]))
        S=add(S,mul(det,prod(L[t] for t in range(len(cycle)) if t not in (i,j))))
    assert mul(D,S)==scale(mul(N,C),2), 'area formula identity'
    sample=tuple(sum((r[i] for r in rays[k]),K()) for i in range(3))
    assert (evaluate(N,sample)/evaluate(D,sample)).sign()>0
    # The ray coordinates verify coverage of C0/C1 exactly:
    # a=z-phi^2*x-phi*y, C0: b=y-x/phi,c=x/phi;
    # C1: b=x-phi*y,c=y.
    xs=tuple(r[0] for r in rays[k]);ys=tuple(r[1] for r in rays[k]);zs=tuple(r[2] for r in rays[k])
    assert vecsub(vecsub(zs,vmul(phi**2,xs)),vmul(phi,ys))==(K(1),K(),K())
    if k==0:
        assert vmul(1/phi,xs)==(K(),K(),K(1))
        assert vecsub(ys,vmul(1/phi,xs))==(K(),K(1),K())
    else:
        assert ys==(K(),K(),K(1))
        assert vecsub(xs,vmul(phi,ys))==(K(),K(1),K())
    # Recompute the degree-10/12 nonnegativity polynomial from the area.
    X,Y,Z=linear([1,0,0]),linear([0,1,0]),linear([0,0,1])
    Q=add(add(power(X,2),power(Y,2)),power(Z,2))
    Fpoly=sub(scale(mul(power(Z,2),power(D,2)),4*phi**6),mul(Q,power(N,2)))
    actual=compose(Fpoly,[xs,ys,zs])
    assert actual==cert,'certificate expansion'
    assert len(cert)==[65,85][k]
    assert all(v.a>=0 and v.b>=0 and v for v in cert.values())
    assert all(sum(m)==[10,12][k] for m in cert)
    assert (0,[10,12][k],0) in cert and (0,0,[10,12][k]) in cert

    # Verify all seven relatively open faces of the ray cone directly, including
    # normals whose slicing plane contains original vertices or full edges.
    # Thus no continuity assertion is needed to validate the area formulas.
    for size in [1,2,3]:
        for active in combinations(range(3),size):
            nr=[rays[k][j] if j in active else (K(),K(),K()) for j in range(3)]
            coords=[tuple(r[i] for r in nr) for i in range(3)]
            dots=[linear(tuple(dot(v,r) for r in nr)) for v in V]
            ss=[evaluate(d,(K(1),K(1),K(1))).sign() for d in dots]
            nodes=[('v',i) for i in range(12) if ss[i]==0]
            nodes += [('e',i,j) for i,j in E if ss[i]*ss[j]<0]
            adj={q:set() for q in nodes}
            for face in faces:
                fn=[q for q in nodes if set(q[1:]).issubset(face)]
                assert len(fn)<=2
                if len(fn)==2:
                    adj[fn[0]].add(fn[1]);adj[fn[1]].add(fn[0])
            assert all(len(v)==2 for v in adj.values())
            order=[min(nodes)]
            order.append(min(adj[order[0]]))
            while True:
                nxt=next(q for q in adj[order[-1]] if q!=order[-2])
                if nxt==order[0]:break
                assert nxt not in order
                order.append(nxt)
            assert len(order)==len(nodes)
            pp=[];ll=[]
            for q in order:
                if q[0]=='v':
                    pp.append([const(v) for v in V[q[1]]]);ll.append(const(1))
                else:
                    i,j=q[1:]
                    pp.append([sub(scale(dots[i],V[j][r]),scale(dots[j],V[i][r])) for r in range(3)])
                    ll.append(sub(dots[i],dots[j]))
            sho={};common=prod(ll)
            for i in range(len(order)):
                j=(i+1)%len(order)
                det=sub(mul(pp[i][0],pp[j][1]),mul(pp[i][1],pp[j][0]))
                sho=add(sho,mul(det,prod(ll[t] for t in range(len(order)) if t not in (i,j))))
            orientation=(evaluate(sho,(K(1),)*3)/evaluate(common,(K(1),)*3)).sign()
            assert orientation in (-1,1)
            sho=scale(sho,orientation)
            nn,dd=compose(N,coords),compose(D,coords)
            if not dd:
                assert k==1 and active==(0,)
                nn,dd=const(2*phi**3),const(1)
            assert mul(dd,sho)==scale(mul(nn,common),2),'boundary area identity'
    print(f'Case {k}: all 7 faces of ray cone checked directly (no continuity needed).')

    print(f'Case {k}: {len(cycle)} section vertices; exact area identity; '
          f'degree {dat["degree"]}, {len(cert)} positive coefficients verified.')

# Maximum hexagon and exact area, with plane z=0.
H=[(phi,K()),(K(1),phi),(-K(1),phi),(-phi,K()),(-K(1),-phi),(K(1),-phi)]
area=sum((H[i][0]*H[(i+1)%6][1]-H[i][1]*H[(i+1)%6][0] for i in range(6)),K())/2
assert area==2*phi**3==K(4,2)
lengths=[dot(vecsub(H[(i+1)%6],H[i]),vecsub(H[(i+1)%6],H[i])) for i in range(6)]
assert lengths.count(K(4))==2 and lengths.count(K(3))==4
print('Maximum hexagon: area 4+2 sqrt(5), 2 squared side lengths 4 and 4 squared side lengths 3.')
print('ALL ICOSAHEDRON CERTIFICATES PASSED.')
