#!/usr/bin/env python3
"""Exact finite certificates for five Platonic-solid realizations.

Arithmetic is the ordered quadratic field Q(sqrt(5)), implemented with exact
Fractions.  There are no floating point operations, tolerances, or numerical
convex hull libraries.  Every noncollinear vertex triple is tested for a
supporting plane; coplanar supporting triples are merged by their vertex set.

Run: python3 code/check_solids.py --output certificates/solids.json

This checks these five finite examples.  It is not a uniqueness proof for all
regular polyhedra, nor a Lean or iPRA kernel verification.
"""
from __future__ import annotations
import argparse
from dataclasses import dataclass
from fractions import Fraction as F
from functools import cmp_to_key
from itertools import combinations, product
import json
from pathlib import Path


@dataclass(frozen=True)
class Q5:
    """a+b*sqrt(5), with rational a,b and exact ordered-field operations."""
    a: F = F(0)
    b: F = F(0)

    def __post_init__(self):
        object.__setattr__(self, "a", F(self.a))
        object.__setattr__(self, "b", F(self.b))

    @staticmethod
    def lift(x):
        return x if isinstance(x, Q5) else Q5(F(x))

    def __add__(self, x):
        x = self.lift(x)
        return Q5(self.a+x.a, self.b+x.b)

    __radd__ = __add__

    def __neg__(self):
        return Q5(-self.a, -self.b)

    def __sub__(self, x):
        return self + (-self.lift(x))

    def __rsub__(self, x):
        return self.lift(x) - self

    def __mul__(self, x):
        x = self.lift(x)
        return Q5(self.a*x.a+5*self.b*x.b, self.a*x.b+self.b*x.a)

    __rmul__ = __mul__

    def inverse(self):
        d = self.a*self.a-5*self.b*self.b
        if d == 0:
            raise ZeroDivisionError("zero element of Q(sqrt(5))")
        return Q5(self.a/d, -self.b/d)

    def __truediv__(self, x):
        return self * self.lift(x).inverse()

    def __rtruediv__(self, x):
        return self.lift(x) / self

    def __pow__(self, n):
        assert isinstance(n, int) and n >= 0
        z = Q5(1)
        for _ in range(n):
            z = z*self
        return z

    def sign(self):
        sa = (self.a > 0) - (self.a < 0)
        sb = (self.b > 0) - (self.b < 0)
        if not sa:
            return sb
        if not sb or sa == sb:
            return sa
        delta = self.a*self.a-5*self.b*self.b
        # Opposite signs reduce comparison to positive squares.
        # A nonzero rational square cannot be five times another rational
        # square (the standard prime-divisibility proof for irrational sqrt5).
        assert delta != 0
        return sa*((delta > 0)-(delta < 0))

    def serial(self):
        return [str(self.a), str(self.b)]

    def __str__(self):
        if not self.b:
            return str(self.a)
        return f"{self.a} + ({self.b})*sqrt(5)"


ZERO = Q5(0)
ONE = Q5(1)
PHI = Q5(F(1,2), F(1,2))
INVPHI = PHI-1


def point(xs):
    return tuple(Q5.lift(x) for x in xs)


def add(u,v):
    return tuple(x+y for x,y in zip(u,v))


def sub(u,v):
    return tuple(x-y for x,y in zip(u,v))


def scale(a,u):
    return tuple(a*x for x in u)


def dot(u,v):
    return sum((x*y for x,y in zip(u,v)), ZERO)


def sq(u):
    return dot(u,u)


def cross(u,v):
    return (u[1]*v[2]-u[2]*v[1],
            u[2]*v[0]-u[0]*v[2],
            u[0]*v[1]-u[1]*v[0])


def cyclic(u):
    return [u, (u[1],u[2],u[0]), (u[2],u[0],u[1])]


def serial_vec(u):
    return [x.serial() for x in u]


def ordered_face(vertices, indices, normal):
    center = scale(Q5(1)/len(indices),
                   tuple(sum((vertices[i][k] for i in indices), ZERO) for k in range(3)))
    u = sub(vertices[indices[0]],center)
    w = cross(normal,u)
    assert sq(u).sign() > 0 and sq(w).sign() > 0
    xy = {i:(dot(u,sub(vertices[i],center)), dot(w,sub(vertices[i],center))) for i in indices}

    def half(q):
        x,y=q
        return 0 if y.sign()>0 or (y.sign()==0 and x.sign()>=0) else 1

    def compare(i,j):
        p,q=xy[i],xy[j]
        hp,hq=half(p),half(q)
        if hp != hq:
            return -1 if hp<hq else 1
        d=(p[0]*q[1]-p[1]*q[0]).sign()
        if d:
            return -d
        assert i==j, "Distinct face vertices have the same centroid ray"
        return 0

    order=sorted(indices,key=cmp_to_key(compare))
    # Convexity and consistent outward orientation, checked at every corner.
    for k,i in enumerate(order):
        j,l=order[(k+1)%len(order)],order[(k+2)%len(order)]
        assert dot(normal,cross(sub(vertices[j],vertices[i]),sub(vertices[l],vertices[j]))).sign()>0
    return order,center


def supporting_faces(vertices):
    faces={}
    triple_count=0
    for i,j,k in combinations(range(len(vertices)),3):
        triple_count+=1
        n=cross(sub(vertices[j],vertices[i]),sub(vertices[k],vertices[i]))
        if sq(n).sign()==0:
            continue
        h=dot(n,vertices[i])
        residual=[dot(n,v)-h for v in vertices]
        signs=[x.sign() for x in residual]
        if all(s<=0 for s in signs):
            pass
        elif all(s>=0 for s in signs):
            n=scale(-1,n)
            h=-h
        else:
            continue
        assert h.sign()>0, "Origin must be strictly interior to every support"
        f=tuple(l for l,v in enumerate(vertices) if (dot(n,v)-h).sign()==0)
        # Normalize to supporting equation n.x=1, preserving outward sign.
        faces[f]=scale(1/h,n)
    return faces,triple_count


def orbit_normals(kind):
    if kind=="tetrahedron":
        return [(point(tuple(-x for x in s)),ONE) for s in product([-1,1],repeat=3) if s[0]*s[1]*s[2]==1]
    if kind=="cube":
        return [(point(tuple(s if j==i else 0 for j in range(3))),ONE) for i in range(3) for s in [-1,1]]
    if kind=="octahedron":
        return [(point(s),ONE) for s in product([-1,1],repeat=3)]
    if kind=="icosahedron":
        out=[(point(s),PHI**2) for s in product([-1,1],repeat=3)]
        for s,t in product([-1,1],repeat=2):
            out.extend((p,PHI**2) for p in cyclic(point((0,s*PHI,t*INVPHI))))
        return out
    if kind=="dodecahedron":
        out=[]
        for s,t in product([-1,1],repeat=2):
            out.extend((p,PHI**2) for p in cyclic(point((0,s*PHI,t))))
        return out
    raise ValueError(kind)


def verify(name,vertices,expected):
    V,E,Faces,p,q=expected
    assert len(vertices)==V and len(set(vertices))==V
    radial={sq(v) for v in vertices}
    assert len(radial)==1 and next(iter(radial)).sign()>0
    support,triples=supporting_faces(vertices)
    assert len(support)==Faces
    face_records=[]
    edges={}
    at_vertex={i:[] for i in range(V)}
    edge_squares=set()
    face_radius_squares=set()
    corner_dots=set()
    face_set_to_index={}
    for number,(indices,normal) in enumerate(sorted(support.items())):
        assert len(indices)==p
        order,center=ordered_face(vertices,indices,normal)
        radii={sq(sub(vertices[i],center)) for i in indices}
        assert len(radii)==1
        face_radius_squares.update(radii)
        face_edges=[]
        for k,i in enumerate(order):
            j=order[(k+1)%p]
            prev=order[(k-1)%p]
            edge=tuple(sorted((i,j)))
            edges.setdefault(edge,[]).append(number)
            face_edges.append(list(edge))
            edge_squares.add(sq(sub(vertices[j],vertices[i])))
            corner_dots.add(dot(sub(vertices[prev],vertices[i]),sub(vertices[j],vertices[i])))
            at_vertex[i].append(number)
        face_set_to_index[indices]=number
        face_records.append({"vertices_ccw_seen_from_outside":order,
            "outward_normal":serial_vec(normal),"support":ONE.serial(),
            "center":serial_vec(center),"circumradius_squared":next(iter(radii)).serial(),
            "edges":face_edges})
    assert len(edges)==E
    assert all(len(fs)==2 for fs in edges.values())
    assert all(len(fs)==q for fs in at_vertex.values())
    assert len(edge_squares)==len(face_radius_squares)==len(corner_dots)==1
    degree=[sum(i in e for e in edges) for i in range(V)]
    assert degree==[q]*V
    assert V-E+Faces==2 and p*Faces==2*E and q*V==2*E
    assert len({i for f in support for i in f})==V

    orbits=[]
    orbit_faces=set()
    for n,h in orbit_normals(name):
        diffs=[(dot(n,v)-h).sign() for v in vertices]
        assert all(s<=0 for s in diffs)
        face=tuple(i for i,s in enumerate(diffs) if s==0)
        assert face in support and len(face)==p
        orbit_faces.add(face)
        orbits.append({"normal":serial_vec(n),"support":h.serial(),
                       "face_index":face_set_to_index[face]})
    assert orbit_faces==set(support)

    # Every listed face is a convex, coplanar, cyclic polygon with equal sides;
    # all corner scalar products agree as an additional regularity certificate.
    return {"name":name,"V":V,"E":E,"F":Faces,"p":p,"q":q,
        "vertices":[serial_vec(v) for v in vertices],
        "edges":[{"vertices":list(e),"incident_faces":fs} for e,fs in sorted(edges.items())],
        "faces":face_records,"incident_faces_at_vertex":at_vertex,
        "vertex_radius_squared":next(iter(radial)).serial(),
        "edge_length_squared":next(iter(edge_squares)).serial(),
        "face_circumradius_squared":next(iter(face_radius_squares)).serial(),
        "face_interior_adjacent_edge_dot":next(iter(corner_dots)).serial(),
        "supporting_normal_orbits":orbits,
        "checked_vertex_triples":triples,
        "checks":{"all_facets_enumerated_via_supporting_vertex_triples":True,
            "all_supporting_faces_have_p_vertices":True,
            "faces_outward_convex_planar_cyclic":True,
            "all_edge_lengths_equal":True,"all_face_corner_dots_equal":True,
            "all_vertex_radii_equal":True,"two_faces_per_edge":True,
            "q_faces_and_edges_at_every_vertex":True,"euler_characteristic_2":True,
            "displayed_normal_orbits_exhaust_faces":True}}


def build():
    assert PHI*PHI==PHI+1 and PHI*INVPHI==ONE
    signs=list(product([-1,1],repeat=3))
    tetra=[point(s) for s in signs if s[0]*s[1]*s[2]==1]
    cube=[point(s) for s in signs]
    octa=[point(tuple(s if j==i else 0 for j in range(3))) for i in range(3) for s in [-1,1]]
    ico=[]
    dodeca=list(cube)
    for s,t in product([-1,1],repeat=2):
        ico.extend(cyclic(point((0,s,t*PHI))))
        dodeca.extend(cyclic(point((0,s*INVPHI,t*PHI))))
    data=[("tetrahedron",tetra,(4,6,4,3,3)),
          ("cube",cube,(8,12,6,4,3)),
          ("octahedron",octa,(6,12,8,3,4)),
          ("icosahedron",ico,(12,30,20,3,5)),
          ("dodecahedron",dodeca,(20,30,12,5,3))]
    return [verify(*item) for item in data]


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--output",type=Path)
    args=p.parse_args()
    solids=build()
    report={"schema":"euclidean-ipra-platonic-certificates-v1",
            "coordinate_format":"Each scalar [a,b] denotes rational a+b*sqrt(5); fractions are exact strings.",
            "indices":"Vertices and faces are zero-based.",
            "arithmetic":"Exact Fraction arithmetic in Q(sqrt(5)); sign decided by rational square comparison.",
            "floating_point":False,"lean_kernel_checked":False,"ipra_kernel_checked":False,
            "scope":"Finite exhaustive realization certificates for the five displayed examples; no general uniqueness theorem.",
            "solids":solids}
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8")
    for s in solids:
        edge=Q5(F(s["edge_length_squared"][0]),F(s["edge_length_squared"][1]))
        print(f"PASS {s['name']}: V={s['V']} E={s['E']} F={s['F']}; (p,q)=({s['p']},{s['q']}); edge^2={edge}")
    print("All supporting triples, face regularity, incidence counts, radii and normal orbits checked exactly.")


if __name__=="__main__":
    main()
