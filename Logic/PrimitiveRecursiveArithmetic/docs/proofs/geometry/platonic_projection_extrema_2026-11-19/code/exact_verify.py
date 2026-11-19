#!/usr/bin/env python3
"""Exact, dependency-free certificates for all five projection extrema.

All decisions use rational arithmetic in Q(phi), phi^2=phi+1, phi>0.
This is an executable certificate check, not a Lean kernel proof.
Run: python3 code/exact_verify.py --output certificates
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import combinations, product
from collections import Counter
from pathlib import Path
import argparse, json

@dataclass(frozen=True)
class K:
    a: Q = Q(0)
    b: Q = Q(0)
    def __post_init__(self):
        object.__setattr__(self, 'a', Q(self.a))
        object.__setattr__(self, 'b', Q(self.b))
    @staticmethod
    def of(v): return v if isinstance(v,K) else K(v)
    def __add__(self,o):
        o=K.of(o); return K(self.a+o.a,self.b+o.b)
    __radd__=__add__
    def __neg__(self): return K(-self.a,-self.b)
    def __sub__(self,o): return self+-K.of(o)
    def __rsub__(self,o): return K.of(o)+-self
    def __mul__(self,o):
        o=K.of(o)
        return K(self.a*o.a+self.b*o.b,
                 self.a*o.b+self.b*o.a+self.b*o.b)
    __rmul__=__mul__
    def inv(self):
        d=self.a*self.a+self.a*self.b-self.b*self.b
        if not d: raise ZeroDivisionError
        return K((self.a+self.b)/d,-self.b/d)
    def __truediv__(self,o): return self*K.of(o).inv()
    def __pow__(self,n):
        if n<0: return self.inv()**(-n)
        r=K(1)
        for _ in range(n): r=r*self
        return r
    def sign(self):
        # 2*(a+b*phi) = c+d*sqrt(5).
        c,d=2*self.a+self.b,self.b
        sg=lambda t:(t>0)-(t<0)
        if not d: return sg(c)
        if not c: return sg(d)
        if sg(c)==sg(d): return sg(c)
        return sg(c)*sg(c*c-5*d*d)
    def __abs__(self): return -self if self.sign()<0 else self
    def __lt__(self,o): return (self-K.of(o)).sign()<0
    def __le__(self,o): return (self-K.of(o)).sign()<=0
    def __float__(self): return float(self.a)+float(self.b)*(1+5**.5)/2
    def encode(self): return [str(self.a),str(self.b)]
    def __str__(self): return f'({self.a})+({self.b})*phi'

Z,K1,P=K(),K(1),K(0,1)
R=P-1
def vec(*v): return tuple(K.of(x) for x in v)
def add(a,b): return tuple(x+y for x,y in zip(a,b))
def sub(a,b): return tuple(x-y for x,y in zip(a,b))
def scale(t,a): return tuple(t*x for x in a)
def dot(a,b): return sum((x*y for x,y in zip(a,b)),Z)
def norm2(a): return dot(a,a)
def cross(a,b):
    return (a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0])
def encv(v): return [x.encode() for x in v]
def canonical_axis(v):
    for x in v:
        if x.sign(): return scale(x.inv(),v)
    raise ValueError('zero axis')
def brightness(gs,x): return sum((abs(dot(g,x)) for g in gs),Z)

T=[vec(1,1,1),vec(1,-1,-1),vec(-1,1,-1),vec(-1,-1,1)]
C=[vec(1,0,0),vec(0,1,0),vec(0,0,1)]
DN=[vec(0,1,P),vec(0,1,-P),vec(1,P,0),vec(1,-P,0),vec(P,0,1),vec(P,0,-1)]
IN=[vec(1,1,1),vec(1,1,-1),vec(1,-1,1),vec(-1,1,1)]
IN += [vec(0,R,s*P) for s in (1,-1)]
IN += [vec(R,s*P,0) for s in (1,-1)]
IN += [vec(P,0,s*R) for s in (1,-1)]

def signed_family(base):
    return [vec(*(s*x for s,x in zip(ss,base))) for ss in product((-1,1),repeat=3)]
def unique(vs): return list(dict.fromkeys(vs))
CV=[vec(*s) for s in product((-1,1),repeat=3)]
OV=[scale(s,e) for e in C for s in (-1,1)]
DV=unique(CV+signed_family((0,P,R))+signed_family((R,0,P))+signed_family((P,R,0)))
IV=unique(signed_family((0,P,1))+signed_family((P,1,0))+signed_family((1,0,P)))

MODELS={
 'tetrahedron':dict(g=T,c=K(Q(1,8)),v=T,e2=K(8),lo=K(8),hi=K(16),umin=vec(1,1,0),umax=vec(1,0,0),faces=4,face_size=3),
 'cube':dict(g=C,c=K1,v=CV,e2=K(4),lo=K(1),hi=K(3),umin=vec(1,0,0),umax=vec(1,1,1),faces=6,face_size=4),
 'octahedron':dict(g=T,c=K(Q(1,4)),v=OV,e2=K(2),lo=K(8),hi=K(16),umin=vec(1,1,0),umax=vec(1,0,0),faces=8,face_size=3),
 'dodecahedron':dict(g=DN,c=(P+2)/4,v=DV,e2=4*(2-P),lo=8+12*P,hi=12+16*P,umin=vec(1,0,0),umax=vec(1,P,0),faces=12,face_size=5),
 'icosahedron':dict(g=IN,c=K(Q(1,4)),v=IV,e2=K(4),lo=20+30*P,hi=24+36*P,umin=vec(1,1,0),umax=vec(1,1,1),faces=20,face_size=3),
}

def enumerate_facets(vertices):
    found=set()
    for i,j,k in combinations(range(len(vertices)),3):
        n=cross(sub(vertices[j],vertices[i]),sub(vertices[k],vertices[i]))
        if norm2(n)==Z: continue
        ds=[dot(n,sub(v,vertices[i])) for v in vertices]
        signs={d.sign() for d in ds}
        if 1 in signs and -1 in signs: continue
        found.add(tuple(t for t,d in enumerate(ds) if d==Z))
    return sorted(found)

def verify_geometry(model):
    vs,e2=model['v'],model['e2']
    assert len({norm2(v) for v in vs})==1
    faces=enumerate_facets(vs)
    assert len(faces)==model['faces']
    edges=set()
    output=[]
    for f in faces:
        assert len(f)==model['face_size']
        neighbors={i:[j for j in f if j!=i and norm2(sub(vs[i],vs[j]))==e2] for i in f}
        assert all(len(ns)==2 for ns in neighbors.values())
        order=[f[0],neighbors[f[0]][0]]
        while len(order)<len(f):
            nxt=next(j for j in neighbors[order[-1]] if j!=order[-2])
            assert nxt not in order
            order.append(nxt)
        assert order[0] in neighbors[order[-1]]
        if len(f)==4:
            assert all(norm2(sub(vs[order[i]],vs[order[(i+2)%4]]))==2*e2 for i in range(4))
        if len(f)==5:
            assert all(norm2(sub(vs[order[i]],vs[order[(i+2)%5]]))==P**2*e2 for i in range(5))
        w=scale(K(Q(1,2))/e2,
                tuple(sum((cross(vs[order[i]],vs[order[(i+1)%len(order)]])[j] for i in range(len(order))),Z) for j in range(3)))
        if dot(w,vs[order[0]]).sign()<0:
            order.reverse();w=scale(-1,w)
        assert dot(w,vs[order[0]]).sign()>0
        for i in range(len(order)): edges.add(tuple(sorted((order[i],order[(i+1)%len(order)]))))
        output.append(dict(vertices=order,unit_edge_area_vector=encv(w)))
    assert len(vs)-len(edges)+len(faces)==2
    actual=[tuple(K(Q(a),Q(b)) for a,b in item['unit_edge_area_vector']) for item in output]
    if len(faces)==len(model['g']):
        # Tetrahedral normals are the negatives of the chosen vertex normals.
        expected=[scale(-2*model['c'],g) for g in model['g']]
    else:
        expected=[scale(s*model['c'],g) for g in model['g'] for s in (-1,1)]
    assert Counter(actual)==Counter(expected),(actual,expected)
    return dict(vertex_count=len(vs),edge_count=len(edges),face_count=len(faces),
                raw_vertices=[encv(v) for v in vs],raw_edge_squared=e2.encode(),facets=output)

def verify_extrema(name,model):
    gs=model['g']; lo,hi=model['lo'],model['hi']
    assert dot(gs[0],cross(gs[1],gs[2]))!=Z
    assert model['c'].sign()>0 and lo.sign()>0 and hi.sign()>0
    signed=[]; maxaxes=set(); maxhist=Counter()
    for signs in product((-1,1),repeat=len(gs)):
        w=tuple(sum((s*g[j] for s,g in zip(signs,gs)),Z) for j in range(3))
        q=norm2(w)
        assert q<=hi
        maxhist[q]+=1
        if q==hi:maxaxes.add(canonical_axis(w))
        signed.append(dict(signs=list(signs),vector=encv(w),squared_norm=q.encode()))
    pairs=[]; minaxes=set(); minhist=Counter()
    for i,j in combinations(range(len(gs)),2):
        w=cross(gs[i],gs[j]); q=norm2(w)
        if q==Z: continue
        h=brightness(gs,w); b2=h*h/q
        assert lo<=b2
        minhist[b2]+=1
        if b2==lo:minaxes.add(canonical_axis(w))
        pairs.append(dict(pair=[i,j],cross=encv(w),norm_squared=q.encode(),
                          brightness=h.encode(),ratio_squared=b2.encode()))
    for key,target in [('umin',lo),('umax',hi)]:
        w=model[key]
        assert brightness(gs,w)**2==target*norm2(w)
    assert minaxes and maxaxes
    def hist(c):return [dict(value=x.encode(),multiplicity=c[x]) for x in sorted(c)]
    return dict(solid=name,normal_representatives=[encv(g) for g in gs],
       area_factor=model['c'].encode(),lower_squared=lo.encode(),upper_squared=hi.encode(),
       unit_edge_min_area_squared=(model['c']**2*lo).encode(),
       unit_edge_max_area_squared=(model['c']**2*hi).encode(),
       minimum_witness=encv(model['umin']),maximum_witness=encv(model['umax']),
       min_axis_count=len(minaxes),max_axis_count=len(maxaxes),
       signed_norm_histogram=hist(maxhist),cross_ratio_histogram=hist(minhist),
       signed_sums=signed,cross_pairs=pairs,geometry=verify_geometry(model))

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',default='certificates'); args=ap.parse_args()
    out=Path(args.output);out.mkdir(parents=True,exist_ok=True)
    summaries=[]
    for name,model in MODELS.items():
        cert=verify_extrema(name,model)
        (out/(name+'.json')).write_text(json.dumps(cert,indent=2)+'\n')
        summary={k:v for k,v in cert.items() if k not in ('signed_sums','cross_pairs','geometry')}
        summaries.append(summary)
        print(name, 'OK',len(cert['signed_sums']),'signed sums,',len(cert['cross_pairs']),
              'cross products; axes',cert['min_axis_count'],cert['max_axis_count'])
        print('  min area^2',model['c']**2*model['lo'],'max area^2',model['c']**2*model['hi'])
        print('  cross ratios:',[(str(K(Q(x['value'][0]),Q(x['value'][1]))),x['multiplicity']) for x in cert['cross_ratio_histogram']])
    (out/'summary.json').write_text(json.dumps(summaries,indent=2)+'\n')
    print('All exact field, facet, signed-sum, cross-product and witness checks passed.')

if __name__=='__main__':main()
