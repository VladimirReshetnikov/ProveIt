#!/usr/bin/env python3
"""Exact finite checks accompanying article.tex.

Requires Python 3.10+ and SymPy. These checks exercise finite rational identities
and examples; they do not verify the general Hahn-field theorems or construct No.
Run from any directory: python code/verify.py
"""
from __future__ import annotations

import json
import platform
import random
from fractions import Fraction
from pathlib import Path
from typing import Iterable

import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
COUNTS: dict[str, int] = {}
T = sp.Symbol("t", positive=True)
RNG = random.Random(20260923)


def check(condition: bool, group: str, detail: str = "") -> None:
    if not condition:
        raise AssertionError(f"{group}: {detail}")
    COUNTS[group] = COUNTS.get(group, 0) + 1


def zero(expr: sp.Expr, group: str, detail: str = "") -> None:
    check(sp.cancel(sp.expand(expr)) == 0, group, detail or str(expr))


def mat_zero(matrix: sp.MatrixBase, group: str) -> None:
    for expr in matrix:
        zero(expr, group)


def val(expr: sp.Expr) -> int | sp.Expr:
    expr = sp.cancel(expr)
    if expr == 0:
        return sp.oo
    num, den = sp.fraction(expr)
    pn, pd = sp.Poly(num, T), sp.Poly(den, T)
    return min(m[0] for m, c in pn.terms()) - min(m[0] for m, c in pd.terms())


def residue(expr: sp.Expr) -> sp.Expr:
    value = val(expr)
    if value == sp.oo or value > 0:
        return sp.Integer(0)
    if value < 0:
        raise ValueError(f"Nonfinite input to residue: {expr}")
    expr = sp.cancel(expr)
    return sp.limit(expr, T, 0, dir="+")


def qmul(q: Iterable[sp.Expr], r: Iterable[sp.Expr]) -> tuple[sp.Expr, ...]:
    a, b, c, d = q
    e, f, g, h = r
    return (a*e-b*f-c*g-d*h, a*f+b*e+c*h-d*g,
            a*g-b*h+c*e+d*f, a*h+b*g-c*f+d*e)


def qmatrix(q: Iterable[sp.Expr]) -> sp.Matrix:
    a, b, c, d = q
    return sp.Matrix([[a+sp.I*b, c+sp.I*d], [-c+sp.I*d, a-sp.I*b]])


def test_gram() -> None:
    group = "leading_Gram_state"
    for k in range(1, 6):
        r1 = T**k * sp.Matrix([[1, T], [0, 1]])
        r2 = T**(k+1) * sp.Matrix([[0, 1], [1, 0]])
        x = r1*r1.T + r2*r2.T
        p = sp.trace(x)
        check(val(p) == 2*k, group)
        zero(residue(p/T**(2*k))-2, group)
        mat_zero((x/p).applyfunc(residue)-sp.eye(2)/2, group)
        a, b = (r1+r2)/sp.sqrt(2), (r1-r2)/sp.sqrt(2)
        mat_zero(a*a.T+b*b.T-x, group)
    # Distinct leading mixed branch, with a coherent cancellation already in R.
    r1 = T**2 * sp.Matrix([[1, 0], [1, T]])
    r2 = T**2 * sp.Matrix([[0, 0], [1, 0]])
    x = r1*r1.T+r2*r2.T
    mat_zero((x/sp.trace(x)).applyfunc(residue)-sp.Matrix([[1,1],[1,2]])/3, group)


def test_postselection() -> None:
    group = "postselection_bound_rational_examples"
    for _ in range(750):
        ra = [RNG.randint(1, 15) for _ in range(5)]
        rb = [RNG.randint(1, 15) for _ in range(5)]
        a = [Fraction(x, sum(ra)) for x in ra]
        b = [Fraction(x, sum(rb)) for x in rb]
        w = [Fraction(RNG.randint(1, 8), 8) for _ in a]
        p = sum(x*y for x, y in zip(a, w))
        q = sum(x*y for x, y in zip(b, w))
        din = sum(abs(x-y) for x, y in zip(a, b))/2
        dout = sum(abs(x*z/p-y*z/q) for x, y, z in zip(a,b,w))/2
        check(max(p,q)*dout <= din, group)
    # Exact saturation with equal success probabilities, for arbitrary real 0<p<1.
    for p in (Fraction(1,2), Fraction(1,17), Fraction(1,1000)):
        rho, eta = [1-p,p,0], [1-p,0,p]
        din = sum(abs(a-b) for a,b in zip(rho,eta))/2
        check(din == p, group)
        check(p*Fraction(1) == din, group)


def test_entanglement() -> None:
    group = "entanglement_filter"
    z = sp.Symbol("z", positive=True)
    psi = sp.Matrix([1,0,0,z])/sp.sqrt(1+z*z)
    filt = sp.diag(z,z,1,1)
    output = filt*psi
    p = 2*z*z/(1+z*z)
    target = sp.Matrix([1,0,0,1])/sp.sqrt(2)
    mat_zero(output*output.T-p*target*target.T, group)
    rho = psi*psi.T
    pt = sp.zeros(4)
    for a in range(2):
        for b in range(2):
            for c in range(2):
                for d in range(2):
                    pt[2*a+d,2*c+b] = rho[2*a+b,2*c+d]
    x = sp.Symbol("x")
    expected = (x-1/(1+z*z))*(x-z*z/(1+z*z))*(x*x-z*z/(1+z*z)**2)
    zero(pt.charpoly(x).as_expr()-expected, group)
    for power in range(1,5):
        check(val(p.subs(z,T**power)) == 2*power, group)
        zero(residue(p.subs(z,T**power)/T**(2*power))-2, group)


def test_schur() -> None:
    group = "Schur_defect_realizations"
    for case in range(24):
        n = 2 + case % 2
        r = 1 + case % 2
        # One regular eliminated mode and r soft modes, at distinct scales.
        q = sp.Matrix(n,n,lambda i,j:RNG.randint(-2,2))
        e = q*q.T
        ell = sp.Matrix(n,r,lambda i,j:RNG.randint(-2,2))
        bh = sp.Matrix(n,1,lambda i,j:RNG.randint(-2,2))
        dh = sp.Integer(2 + case % 3)
        d = sp.diag(dh, *(T**(2*(j+1)) for j in range(r)))
        b = bh.row_join(ell*sp.diag(*(T**(j+1) for j in range(r))))
        a = e+ell*ell.T+bh*bh.T/dh
        schur = a-b*d.inv()*b.T
        mat_zero(schur-e, group)
        b0, d0 = b.applyfunc(residue), d.applyfunc(residue)
        d0plus = sp.diag(1/dh, *([0]*r))
        reduced = a-b0*d0plus*b0.T
        mat_zero(reduced-schur-ell*ell.T, group)
        check((ell*ell.T).rank() <= r, group)
        # Completion of the square, checked as a full block congruence.
        h = a.row_join(b).col_join(b.T.row_join(d))
        l = sp.eye(n).row_join(sp.zeros(n,1+r)).col_join(
            (d.inv()*b.T).row_join(sp.eye(1+r)))
        diagonal = sp.diag(e,d)
        mat_zero(l.T*diagonal*l-h, group)


def test_feshbach() -> None:
    group = "Feshbach_and_soft_spectral_window"
    a, b, z, d = sp.symbols("a b z d", real=True)
    h = sp.Matrix([[a,b*T],[b*T,T*T]])
    f = a-z-b*b*T*T/(T*T-z)
    zero((h-z*sp.eye(2)).det()-(T*T-z)*f, group)
    zero((b*b*d/(d-z)-b*b) - b*b*z/(d-z), group)
    kappa = sp.Symbol("kappa", real=True)
    zero(sp.cancel(f.subs(z,kappa*T*T))-(a-kappa*T*T-b*b/(1-kappa)), group)
    zero(residue(f.subs({a:2,b:1,z:sp.Rational(1,3)}))-sp.Rational(5,3),group)
    zero(residue(f.subs({a:2,b:1,z:0}))-1,group)
    small = (2+T*T-sp.sqrt(4+T**4))/2
    zero(sp.limit(small/(T*T),T,0)-sp.Rational(1,2),group)
    # Scalar positivity threshold: determinant a*t^(2 alpha)-b^2*t^(2 beta).
    for alpha in range(1,5):
        for beta in range(1,5):
            det = 2*T**(2*alpha)-T**(2*beta)
            leading = residue(det/T**val(det))
            check((leading > 0) == (beta >= alpha),group)


def test_quaternions() -> None:
    group = "quaternion_commutator_and_dark_port"
    a,b = sp.symbols("a b", real=True)
    den = (1+a*a)*(1+b*b)
    c = qmul(qmul(qmul((1,a,0,0),(1,0,b,0)),(1,-a,0,0)),(1,0,-b,0))
    c = tuple(sp.cancel(x/den) for x in c)
    zero(sum(x*x for x in c)-1,group)
    p = a*a*b*b/den
    zero(1-c[0]-2*p,group)
    diff = (1-c[0],-c[1],-c[2],-c[3])
    zero(sum(x*x for x in diff)-4*p,group)
    u = qmatrix(c)
    minus,plus = (sp.eye(2)-u)/2,(sp.eye(2)+u)/2
    mat_zero(u.H*u-sp.eye(2),group)
    mat_zero(minus.H*minus-p*sp.eye(2),group)
    mat_zero(minus.H*minus+plus.H*plus-sp.eye(2),group)
    zero(u.det()-1,group)
    for alpha,beta in [(1,1),(1,3),(2,5),(4,2)]:
        subs = {a:T**alpha,b:T**beta}
        pp = p.subs(subs)
        check(val(pp)==2*(alpha+beta),group)
        zero(residue(pp/T**(2*(alpha+beta)))-1,group)
        lead = tuple(residue(x.subs(subs)/T**(alpha+beta)) for x in diff)
        for found,expected in zip(lead,(0,0,0,-2)):
            zero(found-expected,group)
    # Matrix realization respects multiplication, in generic symbolic coordinates.
    q = sp.symbols("q0:4", real=True)
    r = sp.symbols("r0:4", real=True)
    mat_zero(qmatrix(qmul(q,r))-qmatrix(q)*qmatrix(r),group)


def main() -> None:
    test_gram()
    test_postselection()
    test_entanglement()
    test_schur()
    test_feshbach()
    test_quaternions()
    result = {
        "status": "passed",
        "assertions": sum(COUNTS.values()),
        "groups": COUNTS,
        "seed": 20260923,
        "python": platform.python_version(),
        "sympy": sp.__version__,
        "arithmetic": "exact rational / symbolic; no numerical tolerance",
        "scope": "finite examples and identities, not general Hahn-field proofs; no Lean verification"
    }
    path = ROOT / "data" / "verification.json"
    path.parent.mkdir(exist_ok=True)
    path.write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
    print(json.dumps(result,indent=2))


if __name__ == "__main__":
    main()
