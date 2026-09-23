#!/usr/bin/env python3
"""Exact finite algebra checks accompanying the manuscript.

Requires Python >= 3.9 and SymPy. These checks are not a formal verification
of the valuation, normal-subgroup, or proper-class arguments in the article.
Run: python verify.py --output verification.json
"""
from __future__ import annotations
import argparse
import json
import platform
from pathlib import Path
import sympy as sp


def qmul(p: sp.Matrix, q: sp.Matrix) -> sp.Matrix:
    a, b = p[0], q[0]
    u, v = p[1:4, 0], q[1:4, 0]
    return sp.Matrix([a*b-u.dot(v), *(a*v+b*u+u.cross(v))])


def qconj(p: sp.Matrix) -> sp.Matrix:
    return sp.Matrix([p[0], *(-p[1:4, 0])])


def qnorm(p: sp.Matrix) -> sp.Expr:
    return (p.T*p)[0]


def hat(u: sp.Matrix) -> sp.Matrix:
    x, y, z = u
    return sp.Matrix([[0, -z, y], [z, 0, -x], [-y, x, 0]])


def rotation_numerator(p: sp.Matrix) -> sp.Matrix:
    a, u = p[0], p[1:4, 0]
    return (a*a-u.dot(u))*sp.eye(3)+2*u*u.T+2*a*hat(u)


def rational_unit(u: sp.Matrix) -> sp.Matrix:
    r2 = u.dot(u)
    return sp.Matrix([(1-r2)/(1+r2), *(2*u/(1+r2))])


def order_at_zero(expr: sp.Expr, t: sp.Symbol) -> int | sp.Expr:
    expr = sp.cancel(expr)
    if expr == 0:
        return sp.oo
    num, den = sp.fraction(expr)
    pn, pd = sp.Poly(num, t), sp.Poly(den, t)
    return min(m[0] for m in pn.monoms())-min(m[0] for m in pd.monoms())


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, default=Path('verification.json'))
    args = ap.parse_args()
    checks: list[dict[str, object]] = []

    def zero(name: str, expression: sp.Expr | sp.MatrixBase) -> None:
        entries = list(expression) if isinstance(expression, sp.MatrixBase) else [expression]
        if not all(sp.cancel(sp.expand(e)) == 0 for e in entries):
            raise AssertionError(name)
        checks.append({'name': name, 'status': 'pass', 'scalar_identities': len(entries)})

    a, b = sp.symbols('a b', real=True)
    u = sp.Matrix(sp.symbols('u1:4', real=True))
    v = sp.Matrix(sp.symbols('v1:4', real=True))
    p, q = sp.Matrix([a, *u]), sp.Matrix([b, *v])
    pq = qmul(p, q)
    zero('Quaternion norm multiplication', qnorm(pq)-qnorm(p)*qnorm(q))
    zero('Quaternion noncommutativity is twice the cross product', pq-qmul(q,p)-sp.Matrix([0, *(2*u.cross(v))]))
    numerator_comm = qmul(qmul(pq, qconj(p)), qconj(q))
    zero('Unnormalized commutator scalar identity', numerator_comm[0]-(qnorm(p)*qnorm(q)-2*u.cross(v).dot(u.cross(v))))
    Rp, Rq = rotation_numerator(p), rotation_numerator(q)
    zero('Spin matrix scaled orthogonality', Rp.T*Rp-qnorm(p)**2*sp.eye(3))
    zero('Spin matrix determinant', Rp.det()-qnorm(p)**3)
    zero('Spin matrix multiplication', rotation_numerator(pq)-Rp*Rq)
    zero('Skew part of spin matrix', Rp-Rp.T-4*a*hat(u))
    zero('Hat-square identity', hat(u)**2-(u*u.T-u.dot(u)*sp.eye(3)))
    zero('Hat commutator identity', hat(u)*hat(v)-hat(v)*hat(u)-hat(u.cross(v)))

    C = ((1-u.dot(u))*sp.eye(3)+2*u*u.T+2*hat(u))/(1+u.dot(u))
    inverse_coordinates = sp.Matrix([C[2,1]-C[1,2], C[0,2]-C[2,0], C[1,0]-C[0,1]])/(1+sp.trace(C))
    zero('Cayley chart inverse', inverse_coordinates-u)
    zero('Cayley matrix equation', C*(sp.eye(3)-hat(u))-(sp.eye(3)+hat(u)))
    zero('Cayley product numerator', qmul(sp.Matrix([1,*u]),sp.Matrix([1,*v]))-sp.Matrix([1-u.dot(v), *(u+v+u.cross(v))]))

    s = sp.symbols('s', real=True)
    axis_q = sp.Matrix([a,s,0,0])
    power = sp.Matrix([1,0,0,0])
    for m in range(1, 9):
        power = sp.expand(qmul(power, axis_q))
        ratio = sp.cancel(power[1]/s)
        zero(f'Finite power leading coefficient, m={m}', ratio.subs({a:1,s:0})-m)

    t = sp.symbols('t')
    for alpha in range(1, 5):
        for beta in range(1, 5):
            A = rational_unit(sp.Matrix([t**alpha,0,0]))
            B = rational_unit(sp.Matrix([0,t**beta,0]))
            comm = qmul(qmul(qmul(A,B),qconj(A)),qconj(B))
            depth = min(order_at_zero(e,t) for e in comm[1:4,0])
            scalar_depth = order_at_zero(1-comm[0],t)
            if depth != alpha+beta:
                raise AssertionError((alpha,beta,depth))
            if scalar_depth != 2*(alpha+beta):
                raise AssertionError((alpha,beta,scalar_depth))
            checks.append({'name': f'Rational one-parameter commutator depths ({alpha},{beta})',
                           'status':'pass', 'vector_depth':int(depth), 'scalar_defect_depth':int(scalar_depth)})

    ar, ai, br, bi = sp.symbols('ar ai br bi', real=True)
    ac, bc = ar+sp.I*ai, br+sp.I*bi
    r2 = sp.expand(ac*sp.conjugate(ac)+bc*sp.conjugate(bc))
    Bnum = sp.Matrix([[sp.conjugate(ac), sp.conjugate(bc)],[-bc,ac]])
    zero('Unitary Givens scaled orthogonality', Bnum.conjugate().T*Bnum-r2*sp.eye(2))
    zero('Unitary Givens determinant', Bnum.det()-r2)
    zero('Unitary Givens elimination', Bnum*sp.Matrix([ac,bc])-sp.Matrix([r2,0]))

    report = {
        'status':'pass', 'python':platform.python_version(), 'sympy':sp.__version__,
        'number_of_named_checks':len(checks),
        'scope':'Exact polynomial/rational identities and finite one-parameter examples only.',
        'not_verified':['arbitrary real closed fields', 'all valuation cuts', 'normal-subgroup classification',
                        'transfinite series', 'proper-class or universal-quotient theorems', 'Lean formalization'],
        'checks':checks,
    }
    args.output.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(f"PASS: {len(checks)} named exact checks; Python {platform.python_version()}, SymPy {sp.__version__}.")
    print(f'Report written to {args.output.resolve()}')

if __name__ == '__main__':
    main()
