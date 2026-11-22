#!/usr/bin/env python3
"""Exact planar sections over Q(phi), phi^2=phi+1.

Only the Python standard library is required.  No floating point is used in
the section computation, convex hull, comparisons, or squared-area checks.
This is an executable reference implementation, not a Lean proof.
"""
from dataclasses import dataclass
from fractions import Fraction as F
from functools import cmp_to_key
from itertools import product, combinations
import json
from pathlib import Path

@dataclass(frozen=True)
class G:
    a: F = F(0)
    b: F = F(0)
    def __post_init__(self):
        object.__setattr__(self, 'a', F(self.a))
        object.__setattr__(self, 'b', F(self.b))
    @staticmethod
    def of(x):
        return x if isinstance(x, G) else G(x)
    def __add__(self, y):
        y=G.of(y); return G(self.a+y.a,self.b+y.b)
    __radd__=__add__
    def __neg__(self): return G(-self.a,-self.b)
    def __sub__(self,y): return self+-G.of(y)
    def __rsub__(self,y): return G.of(y)+-self
    def __mul__(self,y):
        y=G.of(y)
        return G(self.a*y.a+self.b*y.b,
                 self.a*y.b+self.b*y.a+self.b*y.b)
    __rmul__=__mul__
    def inv(self):
        q=self.a*self.a+self.a*self.b-self.b*self.b
        if not q: raise ZeroDivisionError
        return G((self.a+self.b)/q,-self.b/q)
    def __truediv__(self,y): return self*G.of(y).inv()
    def __rtruediv__(self,y): return G.of(y)*self.inv()
    def __pow__(self,k):
        if k<0: return self.inv()**(-k)
        r=G(1); q=self
        while k:
            if k%2: r=r*q
            q=q*q; k//=2
        return r
    def sign(self):
        # 2(a+b phi)=(2a+b)+b sqrt(5).
        c=2*self.a+self.b; d=self.b
        sg=lambda z: (z>0)-(z<0)
        if not d: return sg(c)
        if not c: return sg(d)
        if sg(c)==sg(d): return sg(c)
        return sg(c)*sg(c*c-5*d*d)
    def __lt__(self,y): return (self-G.of(y)).sign()<0
    def __le__(self,y): return (self-G.of(y)).sign()<=0
    def __gt__(self,y): return (self-G.of(y)).sign()>0
    def __ge__(self,y): return (self-G.of(y)).sign()>=0
    def __float__(self): return float(self.a)+float(self.b)*(1+5**.5)/2
    def data(self): return [str(self.a),str(self.b)]
    def __str__(self): return f'({self.a})+({self.b})*phi'

P=G(0,1)
ZERO=G()
def v(x): return tuple(map(G.of,x))
def add(a,b): return tuple(x+y for x,y in zip(a,b))
def sub(a,b): return tuple(x-y for x,y in zip(a,b))
def scale(t,a): return tuple(t*x for x in a)
def dot(a,b): return sum((x*y for x,y in zip(a,b)),ZERO)
def cross(a,b):
    return (a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0])
def dist2(a,b): return dot(sub(a,b),sub(a,b))

def solids():
    signs=list(product([-1,1],repeat=2))
    T=[v(q) for q in product([-1,1],repeat=3) if q[0]*q[1]*q[2]==1]
    C=[v(q) for q in product([-1,1],repeat=3)]
    O=[v(tuple(s if j==i else 0 for j in range(3))) for i in range(3) for s in [-1,1]]
    I=[v((0,a,b*P)) for a,b in signs]+[v((a,b*P,0)) for a,b in signs]+[v((a*P,0,b)) for a,b in signs]
    D=C+[v((0,a/P,b*P)) for a,b in signs]+[v((a/P,b*P,0)) for a,b in signs]+[v((a*P,0,b/P)) for a,b in signs]
    return {'tetrahedron':T,'cube':C,'octahedron':O,'dodecahedron':D,'icosahedron':I}

def edges(V):
    ds=[(dist2(V[i],V[j]),i,j) for i,j in combinations(range(len(V)),2)]
    m=min(d for d,_,_ in ds)
    return [(i,j) for d,i,j in ds if d==m]

def hull2(points):
    """Monotone-chain hull: projected pair together with original point."""
    points=sorted(set(points),key=lambda p:(p[0],p[1]))
    def orient(a,b,c):
        return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])
    def half(seq):
        h=[]
        for p in seq:
            while len(h)>1 and orient(h[-2],h[-1],p)<=0: h.pop()
            h.append(p)
        return h
    if len(points)<=1: return points
    return half(points)[:-1]+half(reversed(points))[:-1]

def section(V,n,t=G(0),E=None):
    n=v(n); t=G.of(t)
    if not any(x.sign() for x in n): raise ValueError('normal is zero')
    E=edges(V) if E is None else E
    h=[dot(n,p)-t for p in V]
    pts={V[i] for i,x in enumerate(h) if not x.sign()}
    for i,j in E:
        if h[i].sign()*h[j].sign()<0:
            pts.add(scale(1/(h[i]-h[j]),sub(scale(h[i],V[j]),scale(h[j],V[i]))))
    # Dropping any coordinate with nonzero normal gives an injective chart.
    drop=next(i for i in range(3) if n[i].sign())
    axes=[i for i in range(3) if i!=drop]
    planar=[(p[axes[0]],p[axes[1]],p) for p in pts]
    return [q[2] for q in hull2(planar)]

def area2(Q):
    """Squared Euclidean area, from the 3D vector shoelace formula."""
    if len(Q)<3: return G(0)
    w=v((0,0,0))
    for a,b in zip(Q,Q[1:]+Q[:1]): w=add(w,cross(a,b))
    return dot(w,w)/4

def supporting_faces(V):
    """Finite exact supporting-plane enumeration for plotting and audit."""
    faces=set()
    for i,j,k in combinations(range(len(V)),3):
        n=cross(sub(V[j],V[i]),sub(V[k],V[i]))
        if not dot(n,n).sign(): continue
        hs=[dot(n,sub(p,V[i])).sign() for p in V]
        if min(hs)>=0 or max(hs)<=0:
            face=tuple(l for l,h in enumerate(hs) if h==0)
            faces.add(face)
    out=[]
    for ix in sorted(faces):
        a,b,c=(V[ix[i]] for i in range(3))
        n=cross(sub(b,a),sub(c,a))
        drop=next(i for i in range(3) if n[i].sign())
        ax=[i for i in range(3) if i!=drop]
        cycle=hull2([(V[i][ax[0]],V[i][ax[1]],i) for i in ix])
        out.append([q[2] for q in cycle])
    return out

WITNESSES={
 'tetrahedron':((1,1,1),G(-1),G(12),G(8)),
 'cube':((1,1,0),G(0),G(32),G(4)),
 'octahedron':((0,0,1),G(0),G(4),G(2)),
 'dodecahedron':((0,P,1),G(0),G(F(75,4),25),G(8,-4)),
 'icosahedron':((0,0,1),G(0),G(20,32),G(4)),
}

def audit():
    report={}
    for name,V in solids().items():
        n,t,expected,edge2=WITNESSES[name]
        E=edges(V); Q=section(V,n,t,E)
        assert area2(Q)==expected,(name,area2(Q),expected)
        assert all(dist2(V[i],V[j])==edge2 for i,j in E)
        FACES=supporting_faces(V)
        expected_counts={'tetrahedron':(4,6,4),'cube':(8,12,6),'octahedron':(6,12,8),'dodecahedron':(20,30,12),'icosahedron':(12,30,20)}
        assert (len(V),len(E),len(FACES))==expected_counts[name]
        # Uniform geometric margins used by the real-input interpretation.
        assert all(dot(p,p)<=4 for p in V)
        for face in FACES:
            a,b,c=(V[face[i]] for i in range(3))
            normal=cross(sub(b,a),sub(c,a)); support=dot(normal,a)
            assert support*support>=dot(normal,normal)/4
        report[name]={
          'vertices':[[c.data() for c in p] for p in V], 'edges':E,'faces':FACES,
          'normal':[G.of(x).data() for x in n], 'offset':t.data(),
          'section_vertices':[[c.data() for c in p] for p in Q],
          'section_side_squares':[dist2(a,b).data() for a,b in zip(Q,Q[1:]+Q[:1])],
          'area_squared':expected.data(),'edge_squared':edge2.data(),
          'squared_unit_edge_area':(expected/(edge2**2)).data(),
          'inner_ball_radius':'1/2','outer_ball_radius':'2',
        }
        print(f'{name}: V/E/F={len(V)}/{len(E)}/{len(FACES)}, section {len(Q)}-gon; exact A^2={expected}')
    return report

if __name__=='__main__':
    import argparse
    ap=argparse.ArgumentParser();ap.add_argument('--json',type=Path)
    args=ap.parse_args(); r=audit()
    if args.json: args.json.write_text(json.dumps(r,indent=2)+'\n')
