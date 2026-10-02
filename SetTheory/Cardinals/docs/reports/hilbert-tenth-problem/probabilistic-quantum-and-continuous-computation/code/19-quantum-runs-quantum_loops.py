"""Exact finite-dimensional quantum-loop analysis. No floating point arithmetic.

The continuation map must be completely positive and trace nonincreasing.
The routines check square dimensions, rational coordinates, and the index-one
condition; callers supply the physical promise or check it from Kraus matrices.
"""
from __future__ import annotations
from math import factorial
import sympy as sp


def hermitian_basis(d: int) -> list[sp.Matrix]:
    if d < 1:
        raise ValueError("Hilbert dimension must be positive")
    basis = []
    for i in range(d):
        b = sp.zeros(d); b[i, i] = 1; basis.append(b)
    for i in range(d):
        for j in range(i + 1, d):
            b = sp.zeros(d); b[i, j] = b[j, i] = 1; basis.append(b)
            b = sp.zeros(d); b[i, j] = sp.I; b[j, i] = -sp.I; basis.append(b)
    return basis


def coordinates(x: sp.Matrix) -> sp.Matrix:
    if x.rows != x.cols or x != x.conjugate().T:
        raise ValueError("Expected a Hermitian matrix")
    vals = [x[i, i] for i in range(x.rows)]
    for i in range(x.rows):
        for j in range(i + 1, x.rows):
            vals.extend([sp.re(x[i, j]), sp.im(x[i, j])])
    return sp.Matrix(vals).applyfunc(sp.simplify)


def superoperator(kraus: list[sp.Matrix]) -> sp.Matrix:
    if not kraus:
        raise ValueError("At least one Kraus matrix is required")
    d = kraus[0].rows
    if any(k.shape != (d, d) for k in kraus):
        raise ValueError("Kraus dimensions disagree")
    cols = []
    for b in hermitian_basis(d):
        x = sum((k * b * k.conjugate().T for k in kraus), sp.zeros(d))
        cols.append(coordinates(x))
    t = sp.Matrix.hstack(*cols)
    if any(not v.is_Rational for v in t):
        raise ValueError("This implementation requires rational map coordinates")
    return t


def trace_row(d: int) -> sp.Matrix:
    return sp.Matrix([[1] * d + [0] * (d * d - d)])


def group_inverse(t: sp.Matrix) -> tuple[sp.Matrix, sp.Matrix]:
    """Return G=(I-T)# and P, using a rational kernel/image splitting.

    No spectral approximations, eigenvalue choices, or generic-rank assumptions.
    """
    if t.rows != t.cols or t.rows == 0:
        raise ValueError("T must be nonempty and square")
    if any(not v.is_Rational for v in t):
        raise ValueError("T must have rational entries")
    d = t.rows; a = sp.eye(d) - t
    ker, image = a.nullspace(), a.columnspace()
    b = sp.Matrix.hstack(*(ker + image))
    if b.cols != d or b.det() == 0:
        raise ValueError("I-T has nonsemisimple zero: no group inverse")
    r = len(ker); bi = b.inv(); block = bi * a * b
    target = sp.zeros(d)
    if r < d:
        target[r:, r:] = block[r:, r:].inv()
    g = (b * target * bi).applyfunc(sp.cancel)
    p = sp.eye(d) - a * g
    if not (a*g+p == sp.eye(d) and g*a+p == sp.eye(d)
            and a*p == sp.zeros(d) and g*p == sp.zeros(d)):
        raise ArithmeticError("Exact group-inverse verification failed")
    return g, p


def normalized_factorial_moments(t: sp.Matrix, x: sp.Matrix,
                                 exits: sp.Matrix, order: int) -> sp.Matrix:
    """Column k is E[binom(N,k) 1_exit], N=number of continuations.

    Divergent runs contribute zero to these defective, not unconditional, moments.
    """
    if order < 0 or x.shape != (t.rows, 1) or exits.cols != t.rows:
        raise ValueError("Bad moment dimensions or negative order")
    g, _ = group_inverse(t)
    v = g*x; cols = []
    for k in range(order+1):
        cols.append((exits*v).applyfunc(sp.cancel))
        if k != order:
            v = g*t*v
    return sp.Matrix.hstack(*cols)


def stopped_pgf(t: sp.Matrix, x: sp.Matrix, exits: sp.Matrix,
                z: sp.Symbol) -> sp.Matrix:
    return (exits*(sp.eye(t.rows)-z*t).inv()*x).applyfunc(sp.cancel)


def regulator_mean(t: sp.Matrix, x: sp.Matrix, ell: sp.Matrix,
                   epsilon: sp.Symbol) -> sp.Expr:
    return sp.cancel((ell*(sp.eye(t.rows)-(1-epsilon)*t).inv()*x)[0])


def example_data() -> dict[str, dict]:
    q = sp.Rational
    result = {}
    t = sp.Matrix([[q(9,25)]])
    result['scalar_geometric'] = dict(T=t, x=sp.Matrix([1]),
                                    ell=sp.Matrix([[1]]), exits=sp.Matrix([[q(16,25)]]))
    k = sp.diag(1,q(3,5)); h = sp.diag(0,q(4,5)); rho = sp.eye(2)/2
    t = superoperator([k]); ell = trace_row(2)
    result['partial_qubit'] = dict(T=t, x=coordinates(rho), ell=ell,
                                 exits=ell*superoperator([h]), K=k, H=h, rho=rho)
    u = sp.Matrix([[q(3,5),-q(4,5)],[q(4,5),q(3,5)]])
    k = sp.diag(1,q(3,5))*u; h = sp.diag(0,q(4,5))*u
    rho = sp.ones(2)/2; t = superoperator([k])
    result['coherent_qubit'] = dict(T=t, x=coordinates(rho), ell=ell,
                                  exits=ell*superoperator([h]), K=k,H=h,rho=rho)
    k = sp.diag(u,q(3,5)); h=sp.diag(0,0,q(4,5))
    psi=sp.Matrix([1,2,2])/3; rho=psi*psi.T; t=superoperator([k]); ell=trace_row(3)
    result['rotating_dark_qutrit'] = dict(T=t,x=coordinates(rho),ell=ell,
                                       exits=ell*superoperator([h]),K=k,H=h,rho=rho)
    return result
