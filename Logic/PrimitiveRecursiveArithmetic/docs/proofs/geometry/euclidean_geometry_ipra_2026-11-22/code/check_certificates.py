#!/usr/bin/env python3
"""Exact universal polynomial certificates for the Euclidean iPRA report.

This is symbolic coefficient normalization, not numerical sampling.  Every
reported identity is an equality in Z[X_0,...,X_(n-1)].  Evaluation in any
commutative ring preserves these operations, by induction on the expressions.
This executable is independently auditable evidence; it is not a Lean kernel
or an implementation of ProveIt's iPRA proof checker.

Run: python3 code/check_certificates.py --output certificates/polynomials.json
Only the Python standard library is used.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
from typing import Iterable


@dataclass(frozen=True)
class Poly:
    """Canonical sparse polynomial: sorted monomials, nonzero integer coefficients."""
    n: int
    terms: tuple[tuple[tuple[int, ...], int], ...]

    @classmethod
    def from_dict(cls, n: int, d: dict[tuple[int, ...], int]) -> "Poly":
        assert all(len(e) == n and all(k >= 0 for k in e) for e in d)
        return cls(n, tuple(sorted((e, int(c)) for e, c in d.items() if c)))

    @classmethod
    def const(cls, n: int, c: int) -> "Poly":
        return cls.from_dict(n, {(0,) * n: c})

    @classmethod
    def var(cls, n: int, i: int) -> "Poly":
        e = tuple(1 if j == i else 0 for j in range(n))
        return cls.from_dict(n, {e: 1})

    def coerce(self, other: int | "Poly") -> "Poly":
        if isinstance(other, int):
            return Poly.const(self.n, other)
        assert other.n == self.n
        return other

    def __add__(self, other: int | "Poly") -> "Poly":
        other = self.coerce(other)
        d = dict(self.terms)
        for e, c in other.terms:
            d[e] = d.get(e, 0) + c
        return Poly.from_dict(self.n, d)

    __radd__ = __add__

    def __neg__(self) -> "Poly":
        return Poly(self.n, tuple((e, -c) for e, c in self.terms))

    def __sub__(self, other: int | "Poly") -> "Poly":
        return self + (-self.coerce(other))

    def __rsub__(self, other: int | "Poly") -> "Poly":
        return self.coerce(other) - self

    def __mul__(self, other: int | "Poly") -> "Poly":
        other = self.coerce(other)
        d: dict[tuple[int, ...], int] = {}
        for e, c in self.terms:
            for f, b in other.terms:
                g = tuple(x + y for x, y in zip(e, f))
                d[g] = d.get(g, 0) + c * b
        return Poly.from_dict(self.n, d)

    __rmul__ = __mul__

    def __pow__(self, k: int) -> "Poly":
        assert isinstance(k, int) and k >= 0
        out = Poly.const(self.n, 1)
        for _ in range(k):
            out = out * self
        return out

    def degree(self) -> int:
        return max((sum(e) for e, _ in self.terms), default=0)

    def serial(self) -> list[dict]:
        return [{"exponents": list(e), "coefficient": c} for e, c in self.terms]


def variables(names: str) -> tuple[list[str], list[Poly]]:
    ns = names.split()
    return ns, [Poly.var(len(ns), i) for i in range(len(ns))]


def add(u, v):
    return tuple(x + y for x, y in zip(u, v))


def sub(u, v):
    return tuple(x - y for x, y in zip(u, v))


def scale(a, u):
    return tuple(a * x for x in u)


def dot(u, v):
    return sum((x * y for x, y in zip(u, v)), 0)


def sq(u):
    return dot(u, u)


def det(u, v):
    return u[0] * v[1] - u[1] * v[0]


def J(u):
    return -u[1], u[0]


def cmul(u, v):
    return (u[0] * v[0] - u[1] * v[1],
            u[0] * v[1] + u[1] * v[0])


def cross(u, v):
    return (u[1]*v[2] - u[2]*v[1],
            u[2]*v[0] - u[0]*v[2],
            u[0]*v[1] - u[1]*v[0])


def det3(u, v, w):
    return dot(u, cross(v, w))


records: list[dict] = []


def check(name: str, names: list[str], lhs: Poly, rhs: Poly,
          formula: str, interpretation: str) -> None:
    residual = lhs - rhs
    if residual.terms:
        raise AssertionError(f"{name}: nonzero residual {residual.terms}")
    canonical = json.dumps(lhs.serial(), sort_keys=True, separators=(",", ":"))
    records.append({
        "id": name, "variables": names, "formula": formula,
        "interpretation": interpretation, "degree": lhs.degree(),
        "normal_form_terms": len(lhs.terms),
        "normal_form_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
        "lhs_normal_form": lhs.serial(), "rhs_normal_form": rhs.serial(),
        "residual": [], "status": "exact_polynomial_identity",
    })


def check_vector(name, names, lhs, rhs, formula, interpretation):
    for i, (a, b) in enumerate(zip(lhs, rhs)):
        check(f"{name}.{i}", names, a, b, formula + f" [component {i}]", interpretation)


def build_certificates() -> None:
    n, x = variables("ux uy vx vy wx wy t")
    u, v, w, t = x[0:2], x[2:4], x[4:6], x[6]
    z = Poly.const(len(n), 0)
    check("dot_symmetry", n, dot(u, v), dot(v, u),
          "u.v = v.u", "Symmetry of the scalar product")
    check("lagrange_2d", n, sq(u)*sq(v), dot(u,v)**2 + det(u,v)**2,
          "q(u)q(v) = (u.v)^2 + det(u,v)^2", "Cauchy--Schwarz certificate")
    check("polarization", n, sq(sub(u,v)), sq(u)+sq(v)-2*dot(u,v),
          "q(u-v) = q(u)+q(v)-2(u.v)", "Cosine law and Pythagoras")
    check("parallelogram", n, sq(add(u,v))+sq(sub(u,v)), 2*sq(u)+2*sq(v),
          "q(u+v)+q(u-v)=2q(u)+2q(v)", "Parallelogram law")
    check("apollonius", n, 2*sq(sub(u,w))+2*sq(sub(v,w)),
          sq(sub(u,v))+sq(sub(add(u,v),scale(2,w))),
          "2q(u-w)+2q(v-w)=q(u-v)+q(u+v-2w)", "Median theorem, denominators cleared")
    check("quarter_turn_norm", n, sq(J(u)), sq(u), "q(Ju)=q(u)", "Right angle isometry")
    check("quarter_turn_orthogonal", n, dot(u,J(u)), z, "u.Ju=0", "Perpendicular construction")
    check("complex_norm", n, sq(cmul(u,v)), sq(u)*sq(v),
          "q(uv)=q(u)q(v)", "Rotation, similarity and length multiplication")
    check("det_bilinearity", n, det(add(u,v),w), det(u,w)+det(v,w),
          "det(u+v,w)=det(u,w)+det(v,w)", "Area additivity")
    check("affine_area", n, det(sub(v,u),sub(w,u)),
          det(u,v)+det(v,w)+det(w,u),
          "det(v-u,w-u)=det(u,v)+det(v,w)+det(w,u)", "Shoelace triangle formula")
    check_vector("cramer", n, add(scale(det(w,v),u),scale(det(u,w),v)),
                 scale(det(u,v),w),
                 "det(w,v)u+det(u,w)v=det(u,v)w", "Unique line intersections")
    check("det_interpolation", n, det(sub(v,u),sub(add(u,scale(t,sub(w,u))),u)),
          t*det(sub(v,u),sub(w,u)),
          "det(v-u,(u+t(w-u))-u)=t det(v-u,w-u)", "Triangle area ratios")
    check("heron", n,
          2*sq(u)*sq(v)+2*sq(v)*sq(sub(u,v))+2*sq(sub(u,v))*sq(u)
          -sq(u)**2-sq(v)**2-sq(sub(u,v))**2,
          4*det(u,v)**2,
          "2xy+2yz+2zx-x^2-y^2-z^2=4 det(u,v)^2; x=q(u), y=q(v), z=q(u-v)",
          "Heron identity: 16 area^2 equals the side-length polynomial")
    check("stewart_affine", n, sq(sub(w,add(scale(1-t,u),scale(t,v))))
          +t*(1-t)*sq(sub(v,u)),
          (1-t)*sq(sub(w,u))+t*sq(sub(w,v)),
          "q(w-((1-t)u+tv))+t(1-t)q(v-u)=(1-t)q(w-u)+tq(w-v)",
          "Stewart's theorem and weighted variance")
    check("thales", n, 4*dot(sub(w,u),sub(w,v)),
          sq(sub(scale(2,w),add(u,v)))-sq(sub(u,v)),
          "4(w-u).(w-v)=q(2w-u-v)-q(u-v)", "Thales and its converse")
    refl = sub(scale(2*dot(w,u),u),scale(sq(u),w))
    check("reflection_norm", n, sq(refl), sq(u)**2*sq(w),
          "q(2(w.u)u-q(u)w)=q(u)^2 q(w)", "Reflection preserves squared distances")
    foot_num = add(scale(sq(v),u),scale(dot(sub(w,u),v),v))
    check("projection_perpendicular", n, dot(sub(scale(sq(v),w),foot_num),v), z,
          "(q(v)w-q(v)u-((w-u).v)v).v=0", "Foot of perpendicular")
    cnum = sub(scale(sq(v),J(u)),scale(sq(u),J(v)))
    check("circumcenter_u", n, dot(cnum,u), sq(u)*det(u,v),
          "(q(v)Ju-q(u)Jv).u=q(u)det(u,v)", "Circumcenter linear equation")
    check("circumcenter_v", n, dot(cnum,v), sq(v)*det(u,v),
          "(q(v)Ju-q(u)Jv).v=q(v)det(u,v)", "Circumcenter linear equation")
    check("circumradius_numerator", n, sq(cnum), sq(u)*sq(v)*sq(sub(u,v)),
          "q(q(v)Ju-q(u)Jv)=q(u)q(v)q(u-v)", "Circumradius formula, denominators cleared")
    check("orthocenter", n, dot(sub(add(add(u,v),w),u),sub(v,w)), sq(v)-sq(w),
          "(u+v+w-u).(v-w)=q(v)-q(w)", "Orthocenter when circumcenter is the origin")
    check("nine_point", n, sq(sub(add(u,v),add(add(u,v),w))),sq(w),
          "q(u+v-(u+v+w))=q(w)", "Midpoints on the nine-point circle, denominators cleared")

    n, x = variables("px py ox oy vx vy t r")
    p, o, v, t, r = x[:2],x[2:4],x[4:6],x[6],x[7]
    check("line_circle", n, sq(sub(add(p,scale(t,v)),o))-r*r,
          sq(v)*t*t+2*dot(sub(p,o),v)*t+sq(sub(p,o))-r*r,
          "q(p+tv-o)-r^2=q(v)t^2+2(p-o).v t+q(p-o)-r^2", "Line-circle quadratic")

    n, x = variables("px py ox oy cx cy r s")
    p,o,c,r,s=x[:2],x[2:4],x[4:6],x[6],x[7]
    check("radical_axis", n, (sq(sub(p,o))-r*r)-(sq(sub(p,c))-s*s),
          2*dot(p,sub(c,o))+sq(o)-sq(c)-r*r+s*s,
          "Pow_(o,r)(p)-Pow_(c,s)(p)=2p.(c-o)+q(o)-q(c)-r^2+s^2", "Radical axis is linear")

    n,x=variables("ax ay bx by cx cy dx dy")
    a,b,c,d=x[:2],x[2:4],x[4:6],x[6:8]
    check_vector("ptolemy_complex",n,cmul(sub(a,c),sub(b,d)),
                 add(cmul(sub(a,b),sub(c,d)),cmul(sub(a,d),sub(b,c))),
                 "(a-c)(b-d)=(a-b)(c-d)+(a-d)(b-c)",
                 "Ptolemy identity in the complex-coordinate plane")
    check("varignon",n,
          det(add(a,b),add(b,c))+det(add(b,c),add(c,d))
          +det(add(c,d),add(d,a))+det(add(d,a),add(a,b)),
          2*(det(a,b)+det(b,c)+det(c,d)+det(d,a)),
          "shoelace(a+b,b+c,c+d,d+a)=2 shoelace(a,b,c,d)",
          "Varignon midpoint area theorem, denominators cleared")
    check("leibniz_centroid",n,
          3*(sq(sub(d,a))+sq(sub(d,b))+sq(sub(d,c))),
          sq(sub(scale(3,d),add(add(a,b),c)))+sq(sub(a,b))+sq(sub(b,c))+sq(sub(c,a)),
          "3(q(x-a)+q(x-b)+q(x-c))=q(3x-a-b-c)+q(a-b)+q(b-c)+q(c-a)",
          "Leibniz's centroid identity, denominators cleared")

    n,x=variables("ax ay bx by cx cy r s t")
    a,b,c,r,s,t=x[:2],x[2:4],x[4:6],x[6],x[7],x[8]
    check("weighted_norm",n,sq(add(add(scale(r,a),scale(s,b)),scale(t,c))),
          (r+s+t)*(r*sq(a)+s*sq(b)+t*sq(c))
          -r*s*sq(sub(a,b))-s*t*sq(sub(b,c))-t*r*sq(sub(c,a)),
          "q(ra+sb+tc)=(r+s+t)(rq(a)+sq(b)+tq(c))-rsq(a-b)-stq(b-c)-trq(c-a)",
          "Barycentric metric identity and Euler's incenter relation")

    n,x=variables("a b c")
    a,b,c=x
    check("side_angle_order",n,a*(b*b+c*c-a*a)-b*(a*a+c*c-b*b),
          (a-b)*(c*c-(a+b)**2),
          "a(b^2+c^2-a^2)-b(a^2+c^2-b^2)=(a-b)(c^2-(a+b)^2)",
          "Side-angle comparison numerator")
    check("heron_factor",n,4*b*b*c*c-(b*b+c*c-a*a)**2,
          (a+b+c)*(-a+b+c)*(a-b+c)*(a+b-c),
          "4b^2c^2-(b^2+c^2-a^2)^2=(a+b+c)(-a+b+c)(a-b+c)(a+b-c)",
          "Heron's semiperimeter factorization")

    n,x=variables("ux uy uz vx vy vz wx wy wz t")
    u,v,w,t=x[:3],x[3:6],x[6:9],x[9]
    z=Poly.const(len(n),0)
    check("lagrange_3d",n,sq(cross(u,v)),sq(u)*sq(v)-dot(u,v)**2,
          "q(u cross v)=q(u)q(v)-(u.v)^2", "Three-dimensional area and Cauchy--Schwarz")
    check("cross_perpendicular_u",n,dot(u,cross(u,v)),z,
          "u.(u cross v)=0", "Normal to a plane")
    check("cross_perpendicular_v",n,dot(v,cross(u,v)),z,
          "v.(u cross v)=0", "Normal to a plane")
    check("triple_cyclic",n,det3(u,v,w),det3(v,w,u),
          "det(u,v,w)=det(v,w,u)", "Oriented volume cyclic symmetry")
    check("volume_scaling",n,det3(scale(t,u),scale(t,v),scale(t,w)),t**3*det3(u,v,w),
          "det(tu,tv,tw)=t^3 det(u,v,w)", "Volume scaling law")
    check_vector("triple_cross",n,cross(u,cross(v,w)),sub(scale(dot(u,w),v),scale(dot(u,v),w)),
                 "u cross (v cross w)=(u.w)v-(u.v)w", "Vector triple product")
    check("gram_determinant_3d",n,det3(u,v,w)**2,
          sq(u)*sq(v)*sq(w)+2*dot(u,v)*dot(v,w)*dot(w,u)
          -sq(u)*dot(v,w)**2-sq(v)*dot(w,u)**2-sq(w)*dot(u,v)**2,
          "det(u,v,w)^2=det(Gram(u,v,w))", "Volume from metric data")


def main() -> None:
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--output", type=Path)
    args=p.parse_args()
    build_certificates()
    report={
        "schema": "euclidean-ipra-polynomial-certificates-v1",
        "arithmetic": "exact Python integers and sparse monomial coefficient maps",
        "sampling": False,
        "lean_compiled": False,
        "ipra_kernel_checked": False,
        "count": len(records),
        "certificates": records,
    }
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8")
    print(f"PASS: {len(records)} exact polynomial identities; no sampling.")
    print("Scope: universal ring identities only; inequalities, denominators, "
          "geometry hypotheses and iPRA derivations require the report's proofs.")


if __name__ == "__main__":
    main()
