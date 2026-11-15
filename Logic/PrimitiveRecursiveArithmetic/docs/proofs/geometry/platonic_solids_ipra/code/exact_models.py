#!/usr/bin/env python3
"""Exact finite certificates for the five Platonic solids.

All arithmetic is in Q(phi), phi**2 = phi + 1 and phi > 0.
No floating-point, numerical convex-hull library, or symbolic CAS is used.
The program verifies finite geometry; it is not a formal proof in iPRA.
Run: python3 exact_models.py --output certificates.json
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import combinations, permutations, product
import argparse
import json
from pathlib import Path

@dataclass(frozen=True)
class K:
    a: F = F(0)
    b: F = F(0)
    def __post_init__(self):
        object.__setattr__(self, 'a', F(self.a))
        object.__setattr__(self, 'b', F(self.b))
    @staticmethod
    def cast(x): return x if isinstance(x, K) else K(x)
    def __add__(self, y):
        y=K.cast(y); return K(self.a+y.a,self.b+y.b)
    __radd__=__add__
    def __neg__(self): return K(-self.a,-self.b)
    def __sub__(self, y): return self+-K.cast(y)
    def __rsub__(self, y): return K.cast(y)+-self
    def __mul__(self,y):
        y=K.cast(y)
        return K(self.a*y.a+self.b*y.b,
                 self.a*y.b+self.b*y.a+self.b*y.b)
    __rmul__=__mul__
    def inv(self):
        norm=self.a*self.a+self.a*self.b-self.b*self.b
        if not norm: raise ZeroDivisionError
        return K((self.a+self.b)/norm,-self.b/norm)
    def __truediv__(self,y): return self*K.cast(y).inv()
    def __rtruediv__(self,y): return K.cast(y)*self.inv()
    def __pow__(self,k):
        if k<0: return self.inv()**(-k)
        z=K(1)
        for _ in range(k): z=z*self
        return z
    def sign(self):
        # 2(a+b phi)=(2a+b)+b sqrt(5).
        u=2*self.a+self.b; v=self.b
        sg=lambda z: (z>0)-(z<0)
        if not u: return sg(v)
        if not v: return sg(u)
        if sg(u)==sg(v): return sg(u)
        return sg(u)*sg(u*u-5*v*v)
    def __lt__(self,y): return (self-K.cast(y)).sign()<0
    def __le__(self,y): return (self-K.cast(y)).sign()<=0
    def __str__(self):
        if not self.b: return str(self.a)
        if not self.a: return f'({self.b})*phi'
        return f'{self.a}+({self.b})*phi'
    def dump(self): return [str(self.a),str(self.b)]

Z=K(0); O=K(1); PHI=K(0,1)
def vec(x): return tuple(K.cast(v) for v in x)
def add(x,y): return tuple(a+b for a,b in zip(x,y))
def sub(x,y): return tuple(a-b for a,b in zip(x,y))
def scale(c,x): return tuple(c*a for a in x)
def dot(x,y): return sum((a*b for a,b in zip(x,y)),Z)
def cross(x,y):
    return (x[1]*y[2]-x[2]*y[1],x[2]*y[0]-x[0]*y[2],x[0]*y[1]-x[1]*y[0])
def det(x,y,z): return dot(x,cross(y,z))
def norm2(x): return dot(x,x)
def nonzero(x): return any(v!=Z for v in x)
def centroid(vs): return scale(O/len(vs),tuple(sum((v[k] for v in vs),Z) for k in range(3)))
def encode(x):
    if isinstance(x,K): return x.dump()
    if isinstance(x,(list,tuple)): return [encode(v) for v in x]
    if isinstance(x,dict): return {k:encode(v) for k,v in x.items()}
    return x

def coordinate_sets():
    tet=[(1,1,1),(1,-1,-1),(-1,1,-1),(-1,-1,1)]
    cube=list(product((-1,1),repeat=3))
    octa=[]
    for i in range(3):
        for s in (-1,1):
            v=[0,0,0]; v[i]=s; octa.append(tuple(v))
    ico=[]; dod=list(cube)
    for s,t in product((-1,1),repeat=2):
        v=(Z,K(s),t*PHI)
        w=(Z,s*PHI,t*(PHI-O))
        ico.extend(v[i:]+v[:i] for i in range(3))
        dod.extend(w[i:]+w[:i] for i in range(3))
    return {'tetrahedron':list(map(vec,tet)), 'cube':list(map(vec,cube)),
            'octahedron':list(map(vec,octa)), 'dodecahedron':list(map(vec,dod)),
            'icosahedron':list(map(vec,ico))}

def supporting_facets(vertices):
    """Enumerate every potential facet through every vertex triple.

    Completeness: each facet of a full-dimensional finite convex hull contains
    three affinely independent vertices. Each such triple is examined.
    """
    found={}
    for i,j,k in combinations(range(len(vertices)),3):
        n=cross(sub(vertices[j],vertices[i]),sub(vertices[k],vertices[i]))
        if not nonzero(n): continue
        c=dot(n,vertices[i])
        values=[(dot(n,v)-c).sign() for v in vertices]
        if any(s>0 for s in values) and any(s<0 for s in values): continue
        if all(s==0 for s in values): raise AssertionError('Not full dimensional')
        if any(s>0 for s in values): n=scale(-O,n); c=-c
        face=tuple(t for t,v in enumerate(vertices) if dot(n,v)==c)
        found.setdefault(face,(n,c))
    return found

def cyclic_order(vertices,face,n):
    """Boundedly try all orders; require every oriented side to support face."""
    first=min(face)
    for tail in permutations(i for i in face if i!=first):
        cycle=(first,)+tail
        ok=True
        for i,j in zip(cycle,cycle[1:]+cycle[:1]):
            # n is outward; positive signed turns for CCW viewed externally.
            e=sub(vertices[j],vertices[i])
            for k in face:
                if dot(n,cross(e,sub(vertices[k],vertices[i]))).sign()<0:
                    ok=False; break
            if not ok: break
        if ok: return cycle
    raise AssertionError('No convex cyclic order')

def make_symmetries(vertices):
    # Fix a linear basis chosen from the (origin-centered) vertex set.
    basis=next(ids for ids in combinations(range(len(vertices)),3)
               if det(*(vertices[i] for i in ids))!=Z)
    b=[vertices[i] for i in basis]
    denominator=det(*b)
    dual=[scale(O/denominator,cross(b[1],b[2])),
          scale(O/denominator,cross(b[2],b[0])),
          scale(O/denominator,cross(b[0],b[1]))]
    gram=[[dot(x,y) for y in b] for x in b]
    lookup={v:i for i,v in enumerate(vertices)}
    sym=[]
    for ids in permutations(range(len(vertices)),3):
        w=[vertices[i] for i in ids]
        if any(dot(w[i],w[j])!=gram[i][j] for i in range(3) for j in range(3)):
            continue
        matrix=tuple(tuple(sum((w[k][i]*dual[k][j] for k in range(3)),Z)
                           for j in range(3)) for i in range(3))
        imgs=[tuple(dot(row,v) for row in matrix) for v in vertices]
        if not all(v in lookup for v in imgs): continue
        p=tuple(lookup[v] for v in imgs)
        assert len(set(p))==len(vertices)
        # Verify the actual matrix, not merely its candidate Gram test.
        for i in range(3):
            for j in range(3):
                assert sum((matrix[k][i]*matrix[k][j] for k in range(3)),Z)==K(i==j)
        sym.append({'permutation':p,'matrix':matrix})
    return basis,sym

def verify(name,vertices):
    assert len(set(vertices))==len(vertices)
    assert centroid(vertices)==(Z,Z,Z)
    assert any(det(sub(b,a),sub(c,a),sub(d,a))!=Z
               for a,b,c,d in combinations(vertices,4))
    radii={norm2(v) for v in vertices}; assert len(radii)==1
    facets=supporting_facets(vertices)
    faces=[]; planes=[]
    for face,(n,c) in sorted(facets.items()):
        assert c.sign()>0  # origin is strictly within every facet halfspace
        faces.append(cyclic_order(vertices,face,n)); planes.append((n,c))
    p=len(faces[0]); assert p>=3 and all(len(f)==p for f in faces)
    edge_faces={}
    length=None; face_grams=[]
    for fi,face in enumerate(faces):
        n,c=planes[fi]
        assert all(dot(n,v)<=c for v in vertices)
        assert {i for i,v in enumerate(vertices) if dot(n,v)==c}==set(face)
        mids=centroid([vertices[i] for i in face])
        rel=[sub(vertices[i],mids) for i in face]
        G=[[dot(x,y) for y in rel] for x in rel]
        assert all(G[i][j]==G[(i+1)%p][(j+1)%p] for i in range(p) for j in range(p))
        # The cyclic permutation is an isometry of the affine face plane,
        # hence a rotation taking each vertex to the next: regular polygon.
        face_grams.append(G)
        for i,j in zip(face,face[1:]+face[:1]):
            e=tuple(sorted((i,j))); edge_faces.setdefault(e,[]).append(fi)
            ell=norm2(sub(vertices[i],vertices[j]))
            if length is None: length=ell
            assert ell==length and ell.sign()>0
    assert all(g==face_grams[0] for g in face_grams)
    edges=sorted(edge_faces)
    assert all(len(fs)==2 for fs in edge_faces.values())
    vertex_faces=[sorted(fi for fi,f in enumerate(faces) if v in f) for v in range(len(vertices))]
    q=len(vertex_faces[0]); assert q>=3 and all(len(fs)==q for fs in vertex_faces)
    assert all(sum(v in e for e in edges)==q for v in range(len(vertices)))
    # Links are simple cycles, checked by walking face adjacency at each vertex.
    for v,fs in enumerate(vertex_faces):
        link={f:[] for f in fs}
        for e,ef in edge_faces.items():
            if v in e:
                a,b=ef; link[a].append(b); link[b].append(a)
        assert all(len(nbs)==2 and len(set(nbs))==2 for nbs in link.values())
        seen={fs[0]}; frontier=[fs[0]]
        for _ in range(len(fs)):
            frontier=[b for a in frontier for b in link[a] if b not in seen]
            seen.update(frontier)
        assert seen==set(fs)
    V,E,Fc=len(vertices),len(edges),len(faces)
    assert V+Fc==E+2 and p*Fc==2*E==q*V
    basis,symmetries=make_symmetries(vertices)
    face_index={frozenset(f):i for i,f in enumerate(faces)}
    flags={(v,tuple(e),fi) for e,fs in edge_faces.items() for fi in fs for v in e}
    baseflag=min(flags)
    images=set()
    for s in symmetries:
        perm=s['permutation']; v,e,f=baseflag
        target=(perm[v],tuple(sorted(perm[a] for a in e)),
                face_index[frozenset(perm[a] for a in faces[f])])
        images.add(target)
    assert images==flags and len(symmetries)==len(flags)==4*E
    record={'name':name,'field':'Q(phi), phi^2=phi+1, phi>0',
            'vertices':vertices,'faces':faces,'support_planes':[{'normal':n,'constant':c} for n,c in planes],
            'edges':edges,'vertex_faces':vertex_faces,'p':p,'q':q,'V':V,'E':E,'F':Fc,
            'edge_length_squared':length,'circumradius_squared':next(iter(radii)),
            'representative_face_gram':face_grams[0],
            'symmetry_basis':basis,'symmetries':symmetries,'flag_count':len(flags)}
    print(f'{name:13s} p={p} q={q} V={V:2} E={E:2} F={Fc:2} '
          f'edge^2={length} R^2={next(iter(radii))} symmetries={len(symmetries)}')
    print('  face:',faces[0],'; plane:',tuple(map(str,planes[0][0])),'=',str(planes[0][1]))
    return record

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,default=Path('certificates.json'))
    args=ap.parse_args()
    assert PHI*PHI==PHI+O and PHI.sign()==1 and (PHI-O).sign()==1
    sets=coordinate_sets()
    records=[verify(name,vs) for name,vs in sets.items()]
    # Independently normalize both golden-ratio models' complete facet lists.
    byname={r['name']:r for r in records}
    for name,dualname in [('icosahedron','dodecahedron'),('dodecahedron','icosahedron')]:
        vs=sets[name]; c=PHI**2
        expected=set()
        for n in sets[dualname]:
            assert all(dot(n,v)<=c for v in vs)
            expected.add(frozenset(i for i,v in enumerate(vs) if dot(n,v)==c))
        actual={frozenset(f) for f in byname[name]['faces']}
        assert expected==actual
    assert {(r['p'],r['q']) for r in records}=={(3,3),(4,3),(3,4),(5,3),(3,5)}
    args.output.write_text(json.dumps(encode({'format_version':1,'solids':records}),indent=2)+'\n')
    print(f'PASS: exact supporting facets, convex regular faces, links, incidence, Euler, and flag transitivity. Wrote {args.output}')

if __name__=='__main__': main()
