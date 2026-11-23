#!/usr/bin/env python3
"""Exact symbolic diagnostics for the circle chapter.

These checks verify polynomial/rational identities over Q.  They do not
constitute an iPRA or Lean formalization and do not verify inequality or
geometric branch arguments; those are given in the human-readable proofs.
Run with Python 3 and SymPy 1.13 or later.
"""

import sympy as sp


def dot(u, v):
    return u[0] * v[0] + u[1] * v[1]


def det(u, v):
    return u[0] * v[1] - u[1] * v[0]


def q(u):
    return dot(u, u)


def add(u, v):
    return tuple(x + y for x, y in zip(u, v))


def sub(u, v):
    return tuple(x - y for x, y in zip(u, v))


def scale(a, u):
    return tuple(a * x for x in u)


def quarter(u):
    return (-u[1], u[0])


def mul(u, v):
    return (u[0] * v[0] - u[1] * v[1], u[0] * v[1] + u[1] * v[0])


def conj(u):
    return (u[0], -u[1])


checked = []


def verify(name, expressions, ideal=None):
    if not isinstance(expressions, (tuple, list)):
        expressions = (expressions,)
    for expression in expressions:
        numerator = sp.cancel(expression).as_numer_denom()[0]
        residual = sp.expand(numerator)
        if ideal is not None:
            residual = ideal.reduce(residual)[1]
        if residual != 0:
            raise AssertionError(f"{name}: nonzero residual {residual}")
    checked.append(name)


ux, uy, vx, vy, px, py, rho, t, k = sp.symbols("ux uy vx vy px py rho t k")
u, v, p = (ux, uy), (vx, vy), (px, py)

verify("Lagrange identity", q(u) * q(v) - dot(u, v) ** 2 - det(u, v) ** 2)
verify("pair norm multiplicativity", q(mul(u, v)) - q(u) * q(v))

aa, bb, cc = q(v), dot(p, v), q(p) - rho
disc = bb ** 2 - aa * cc
verify("line-circle completion of square",
       aa * (q(add(p, scale(t, v))) - rho) - (aa * t + bb) ** 2 + disc)

verify("Thales diameter identity", dot(sub(u, p), sub(v, p))
       - q(sub(p, scale(sp.Rational(1, 2), add(u, v))))
       + q(sub(v, u)) / 4)

verify("circle chord interpolation identity",
       q(add(scale(1 - t, u), scale(t, v)))
       - (1 - t) * q(u) - t * q(v) + t * (1 - t) * q(sub(v, u)))

dx, dy, r1, r2, sroot = sp.symbols("dx dy r1 r2 sroot")
d = (dx, dy)
s = q(d)
E = 4 * s * r1 - (s + r1 - r2) ** 2
h = scale((s + r1 - r2) / (2 * s), d)
candidate = add(h, scale(sroot / (2 * s), quarter(d)))
root_ideal = sp.groebner([sroot ** 2 - E], sroot, dx, dy, r1, r2)
verify("circle-circle first radius", q(candidate) - r1, root_ideal)
verify("circle-circle second radius", q(sub(candidate, d)) - r2, root_ideal)

R1, R2, delta = sp.symbols("R1 R2 delta")
verify("circle-circle radius factorization",
       4 * delta ** 2 * R1 ** 2 - (delta ** 2 + R1 ** 2 - R2 ** 2) ** 2
       - ((R1 + R2) ** 2 - delta ** 2) * (delta ** 2 - (R1 - R2) ** 2))

zroot = sp.symbols("zroot")
tangent = add(scale(rho / q(p), p), scale(zroot / q(p), quarter(p)))
tangent_ideal = sp.groebner([zroot ** 2 - rho * (q(p) - rho)],
                           zroot, px, py, rho)
verify("external tangent circle membership", q(tangent) - rho, tangent_ideal)
verify("external tangent orthogonality", dot(sub(p, tangent), tangent), tangent_ideal)

ax, ay, bx, by = sp.symbols("ax ay bx by")
a, b = (ax, ay), (bx, by)
up, vp = sub(a, p), sub(b, p)
circle_ideal = sp.groebner([q(a) - rho, q(b) - rho, q(p) - rho],
                          ax, ay, bx, by, px, py, rho)
inscribed_lhs = scale(rho, mul(mul(conj(up), vp), mul(conj(up), vp)))
inscribed_rhs = scale(q(up) * q(vp), mul(conj(a), b))
verify("inscribed central-angle polynomial identity",
       sub(inscribed_lhs, inscribed_rhs), circle_ideal)

unit_parameter = ((1 - t ** 2) / (1 + t ** 2), 2 * t / (1 + t ** 2))
verify("rational circle parametrization", q(unit_parameter) - 1)

verify("inversion distance numerator", q(sub(scale(q(v), u), scale(q(u), v)))
       - q(u) * q(v) * q(sub(u, v)))

cx, cy = sp.symbols("cx cy")
c = (cx, cy)
verify("Ptolemy pair identity", sub(mul(c, sub(d, b)),
       add(mul(b, sub(d, c)), mul(d, sub(c, b)))))

bp, dp = b, d
cp = add(scale(1 - t, bp), scale(t, dp))
binv, cinv, dinv = scale(1 / q(bp), bp), scale(1 / q(cp), cp), scale(1 / q(dp), dp)
verify("Ptolemy converse orientation",
       det(sub(cinv, binv), sub(dinv, binv))
       - det(bp, dp) * t * (1 - t) * q(sub(dp, bp)) / (q(bp) * q(cp) * q(dp)))

ca, cb, c0 = sp.symbols("ca cb c0")
ad_intercept = ca * cb * det(u, v) / (cb * vy - ca * uy)
verify("butterfly side-line intercept",
       det(sub((ad_intercept, 0), scale(ca, u)), sub(scale(cb, v), scale(ca, u))))
verify("butterfly cancellation from Vieta",
       (-c0 / q(v)) * (2 * k * uy / q(u)) * vy
       - (-c0 / q(u)) * (2 * k * vy / q(v)) * uy)

print(f"PASS: {len(checked)} exact symbolic identity groups")
for item in checked:
    print(f"  {item}")
print("Scope: algebraic diagnostics only; inequalities, branch conditions, and iPRA proof compilation are not tested here.")
