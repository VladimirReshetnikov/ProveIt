#!/usr/bin/env python3
"""Exact finite-algebra checks for Rotations of Surreal Three-Space.

Requires Python >= 3.9 and SymPy >= 1.12. No network access is used.
These checks are polynomial/rational identities and finite specializations;
they are not a formal verification of the surreal or topological theorems.
"""
from __future__ import annotations

import itertools
import platform
import time
from typing import Iterable

import sympy as s

I = s.eye(3)
checks = 0


def hat(v: s.Matrix) -> s.Matrix:
    """Right-handed cross-product matrix for a three-component column."""
    if v.shape != (3, 1):
        raise ValueError("hat expects a 3-by-1 column")
    x, y, z = v
    return s.Matrix([[0, -z, y], [z, 0, -x], [-y, x, 0]])


def quat_mul(p: s.Matrix, q: s.Matrix) -> s.Matrix:
    if p.shape != (4, 1) or q.shape != (4, 1):
        raise ValueError("quaternions must be 4-by-1 columns")
    a, b = p[0], q[0]
    u, v = s.Matrix(p[1:]), s.Matrix(q[1:])
    return s.Matrix([a * b - u.dot(v), *(a * v + b * u + u.cross(v))])


def quat_conj(q: s.Matrix) -> s.Matrix:
    return s.Matrix([q[0], -q[1], -q[2], -q[3]])


def norm_square(q: s.Matrix) -> s.Expr:
    return q.dot(q)


def rotation_numerator(q: s.Matrix) -> s.Matrix:
    """N(q) times the rotation matrix of a nonzero quaternion."""
    a, u = q[0], s.Matrix(q[1:])
    return (a*a - u.dot(u))*I + 2*u*u.T + 2*a*hat(u)


def cayley_num(t: s.Matrix) -> s.Matrix:
    return (1 - t.dot(t))*I + 2*t*t.T + 2*hat(t)


def expressions(value: object) -> Iterable[s.Expr]:
    if isinstance(value, s.MatrixBase):
        return list(value)
    return [s.sympify(value)]


def check(name: str, value: object) -> None:
    global checks
    for i, expression in enumerate(expressions(value)):
        numerator = s.together(expression).as_numer_denom()[0]
        if s.expand(numerator) != 0:
            raise AssertionError(f"{name}, component {i}: {s.factor(numerator)}")
    checks += 1
    print(f"PASS {checks:02d}: {name}")


def main() -> None:
    global checks
    start = time.perf_counter()
    print(f"Python {platform.python_version()}; SymPy {s.__version__}")
    print("Exact identities; no floating-point approximations.\n")
    u = s.Matrix(s.symbols("u1:4"))
    v = s.Matrix(s.symbols("v1:4"))
    check("hat square identity", hat(u)**2 - u*u.T + u.dot(u)*I)
    check("hat cube identity", hat(u)**3 + u.dot(u)*hat(u))
    check("Lie bracket equals cross product", hat(u)*hat(v)-hat(v)*hat(u)-hat(u.cross(v)))

    p = s.Matrix(s.symbols("p0:4"))
    q = s.Matrix(s.symbols("q0:4"))
    pq = quat_mul(p, q)
    rquat = s.Matrix(s.symbols("r0:4"))
    check("quaternion associativity", quat_mul(pq,rquat)-quat_mul(p,quat_mul(q,rquat)))
    def complex_matrix(z: s.Matrix) -> s.Matrix:
        a,b,c,d = z
        return s.Matrix([[a+s.I*b,c+s.I*d],[-c+s.I*d,a-s.I*b]])
    check("faithful complex-matrix multiplication formula", complex_matrix(pq)-complex_matrix(p)*complex_matrix(q))
    check("quaternion norm is multiplicative", norm_square(pq)-norm_square(p)*norm_square(q))
    check("quaternion conjugation reverses multiplication", quat_conj(pq)-quat_mul(quat_conj(q), quat_conj(p)))
    R = rotation_numerator(p)
    check("quaternion rotation numerator is scaled orthogonal", R.T*R-norm_square(p)**2*I)
    check("quaternion rotation composition", rotation_numerator(pq)-R*rotation_numerator(q))

    M, D = cayley_num(u), 1+u.dot(u)
    check("Cayley orthogonality", M.T*M-D**2*I)
    check("Cayley determinant one", M.det()-D**3)
    check("Cayley inverse matrix identity", M-D*I-(M+D*I)*hat(u))
    check("Cayley trace identity", s.trace(M)+D-4)
    check("Cayley exceptional-locus determinant", (M+D*I).det()-8*D**2)
    prod = s.Matrix([1-u.dot(v), *(u+v+u.cross(v))])
    check("Cayley product polynomial identity", M*cayley_num(v)-rotation_numerator(prod))
    check("Cayley product denominator identity", norm_square(prod)-D*(1+v.dot(v)))

    a, b, x, y = s.symbols("a b x y")
    P, Q = s.Matrix([a,x,0,0]), s.Matrix([b,0,y,0])
    comm_num = quat_mul(quat_mul(quat_mul(P,Q),quat_conj(P)),quat_conj(Q))
    check("commutator scalar used in perfectness proof", comm_num[0]-(a*a+x*x)*(b*b+y*y)+2*x*x*y*y)

    e, d = s.symbols("epsilon delta")
    e1, e2, e3 = I[:,0], I[:,1], I[:,2]
    num = cayley_num(e*e1)*cayley_num(d*e2)*cayley_num(-e*e1)*cayley_num(-d*e2)
    den = (1+e*e)**2*(1+d*d)**2
    remainder = num-den*(I+4*e*d*hat(e3))
    for item in remainder:
        for (i,j), coefficient in s.Poly(s.expand(item),e,d).terms():
            if coefficient != 0 and not (i >= 1 and j >= 1 and i+j >= 3):
                raise AssertionError("Incorrect commutator leading term/remainder")
    checks += 1
    print(f"PASS {checks:02d}: two-scale commutator and mixed-degree remainder")

    c, sn = s.symbols("c sn")
    r = s.symbols("r", nonzero=True)
    hx, hy, hz = s.symbols("hx hy hz")
    n, h = e3, s.Matrix([hx,hy,hz])
    dn = s.Matrix([hx/r,hy/r,0])
    A = c*I+(1-c)*n*n.T+sn*hat(n)
    dA = -sn*hz*I+sn*hz*n*n.T+(1-c)*(dn*n.T+n*dn.T)+c*hz*hat(n)+sn*hat(dn)
    J = I+(1-c)/r*hat(n)+(r-sn)/r*hat(n)**2
    difference = dA*A.T-hat(J*h)
    for item in difference:
        num = s.together(item).as_numer_denom()[0]
        if s.expand(s.rem(s.expand(num), c*c+sn*sn-1, c)) != 0:
            raise AssertionError("Jacobian does not agree modulo c^2+sn^2=1")
    checks += 1
    print(f"PASS {checks:02d}: right-trivialized derivative in an axis-adapted frame")
    k = (sn*sn+(1-c)**2)/r**2
    check("Jacobian determinant", J.det()-k)
    check("Jacobian squared singular values", J.T*J-s.diag(k,k,1))
    check("Jacobian determinant circle reduction", k-2*(1-c)/r**2-(c*c+sn*sn-1)/r**2)

    # A finite exact representation check, not a claim of surreal evaluation.
    octa = []
    for perm in itertools.permutations(range(3)):
        for signs in itertools.product((-1,1), repeat=3):
            A = s.zeros(3)
            for j in range(3):
                A[perm[j],j] = signs[j]
            if A.det() == 1:
                octa.append(A)
    keys = {tuple(A) for A in octa}
    assert len(keys) == 24
    assert all(tuple(A*B) in keys for A in octa for B in octa)
    checks += 1
    print(f"PASS {checks:02d}: all 576 products of the 24-element octahedral group")
    t = s.Matrix([s.Rational(1,7),s.Rational(1,49),0])
    C = cayley_num(t)/(1+t.dot(t))
    deformed = [C*A*C.T for A in octa]
    B = sum((g*A.T for g,A in zip(deformed,octa)), s.zeros(3))/24
    for g,A in zip(deformed,octa):
        if g*B != B*A:
            raise AssertionError("Finite averaging intertwiner failed")
    checks += 1
    print(f"PASS {checks:02d}: averaging intertwiner for an exact rational conjugate")
    print(f"\nAll {checks} checks passed in {time.perf_counter()-start:.2f} seconds.")
    print("Scope: finite symbolic identities and finite rational tests only.")
    print("Not a Lean proof, a proof of Hahn summability, or a topological verification.")


if __name__ == "__main__":
    main()
