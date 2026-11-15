#!/usr/bin/env python3
"""Exact symbolic checks for the Euler/Rodrigues algebraic core.

This checks finite polynomial identities over QQ, not a formal iPRA proof.
No floating point numbers, eigenvalue calculations, or genericity assumptions
are used.  Run with Python 3 and SymPy.
"""

import json
import sympy as sp


def check_zero(name, expression):
    entries = list(expression) if isinstance(expression, sp.MatrixBase) else [expression]
    for entry in entries:
        assert sp.expand(entry) == 0, (name, sp.expand(entry))
    checks.append(name)


def reduce_zero(name, expression, ideal):
    entries = list(expression) if isinstance(expression, sp.MatrixBase) else [expression]
    for entry in entries:
        remainder = ideal.reduce(sp.expand(entry))[1]
        assert remainder == 0, (name, remainder)
    checks.append(name)


def cross_matrix(v):
    x, y, z = v
    return sp.Matrix([[0, -z, y], [z, 0, -x], [-y, x, 0]])


checks = []
I = sp.eye(3)
r = sp.symbols("r00:03 r10:13 r20:23")
R = sp.Matrix(3, 3, r)
t = sp.trace(R)
e2 = sp.trace(R.adjugate())

check_zero("adjugate_coefficient_identity", R.adjugate() - (R**2 - t * R + e2 * I))
check_zero("shifted_adjugate", (I-R).adjugate() - ((1-t) * I + R + R.adjugate()))
check_zero("shifted_determinant", (I-R).det() - (1-t+e2-R.det()))
check_zero("adjugate_product_left", R * R.adjugate() - R.det() * I)
check_zero("adjugate_product_right", R.adjugate() * R - R.det() * I)
check_zero("double_adjugate", R.adjugate().adjugate() - R.det() * R)

u = sp.Matrix(sp.symbols("u0:3"))
v = sp.Matrix(sp.symbols("v0:3"))
w = sp.Matrix(sp.symbols("w0:3"))
U = cross_matrix(u)
check_zero("cross_square", U**2 - (u*u.T-u.dot(u)*I))
check_zero("vector_triple_product", U * cross_matrix(v) * w - (v*u.dot(w) - w*u.dot(v)))
check_zero("cross_is_skew", U.T + U)
check_zero("cross_kills_axis", U*u)
check_zero("cross_norm_identity", (U*v).dot(U*v) - (u.dot(u)*v.dot(v)-u.dot(v)**2))

c, s = sp.symbols("c s")
P = c*I+(1-c)*u*u.T+s*U
axis_ideal = sp.groebner([u.dot(u)-1], *u, c, s, domain=sp.QQ)
circle_axis_ideal = sp.groebner([u.dot(u)-1, c*c+s*s-1], *u, c, s, domain=sp.QQ)
reduce_zero("rodrigues_fixes_axis", P*u-u, axis_ideal)
reduce_zero("rodrigues_orthogonal", P.T*P-I, circle_axis_ideal)
reduce_zero("rodrigues_determinant_one", P.det()-1, circle_axis_ideal)
reduce_zero("rodrigues_trace", sp.trace(P)-(1+2*c), axis_ideal)
reduce_zero("rodrigues_skew_part", P-P.T-2*s*U, axis_ideal)
reduce_zero("rodrigues_symmetric_axis_part", (P+P.T)/2-c*I-(1-c)*u*u.T, axis_ideal)

check_zero("finite_frobenius_expansion", sp.trace((R-I).T*(R-I))-(sp.trace(R.T*R)-2*t+3))

h = sp.symbols("h")
check_zero("general_rodrigues_determinant",
           (c*I+h*u*u.T+s*U).det()-(c+h*u.dot(u))*(c*c+s*s*u.dot(u)))

# Homogeneous quaternion numerator, without dividing by its positive norm.
a, x, y, z = sp.symbols("a x y z")
vquat = sp.Matrix((x, y, z))
Dquat = a*a+vquat.dot(vquat)
Mquat = (a*a-vquat.dot(vquat))*I+2*vquat*vquat.T+2*a*cross_matrix(vquat)
check_zero("quaternion_numerator_orthogonality", Mquat.T*Mquat-Dquat**2*I)
check_zero("quaternion_numerator_determinant", Mquat.det()-Dquat**3)

# The precise (1,x,y,0) Cayley family used in the LLPO reduction.
K = cross_matrix(sp.Matrix((x, y, 0)))
D = 1+x*x+y*y
M = sp.Matrix([[1+x*x-y*y, 2*x*y, 2*y],
               [2*x*y, 1-x*x+y*y, -2*x],
               [-2*y, 2*x, 1-x*x-y*y]])
check_zero("cayley_equals_quaternion_numerator", M-Mquat.subs({a:1,z:0}))
check_zero("cayley_numerator_expansion", M-(D*I+2*(K+K*K)))
check_zero("cayley_factorization", (I-K)*M-D*(I+K))
check_zero("cayley_cross_cube", K**3+(x*x+y*y)*K)
check_zero("cayley_left_factor_determinant", (I-K).det()-D)
check_zero("cayley_right_factor_determinant", (I+K).det()-D)

print(json.dumps({"status": "passed", "arithmetic": "exact rational polynomial arithmetic", "checks": checks}, indent=2))
