#!/usr/bin/env python3
"""Exact finite checks accompanying the surquaternion article.

Run: python3 verify.py
Requires: Python 3.9+ and SymPy. No network access or floating-point data.
This checks displayed algebraic identities and finite truncations; it does
not constitute a formal proof of class-sized or infinite-support theorems.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Callable, Sequence, Tuple

try:
    import sympy as s
except ImportError as exc:
    raise SystemExit("SymPy is required. Install it with: python -m pip install sympy") from exc

Quat = Tuple[s.Expr, s.Expr, s.Expr, s.Expr]
Z: Quat = (s.S.Zero,) * 4
ONE: Quat = (s.S.One, s.S.Zero, s.S.Zero, s.S.Zero)
I: Quat = (s.S.Zero, s.S.One, s.S.Zero, s.S.Zero)
J: Quat = (s.S.Zero, s.S.Zero, s.S.One, s.S.Zero)
K: Quat = (s.S.Zero, s.S.Zero, s.S.Zero, s.S.One)
t = s.Symbol("t")
records = []


def add(p: Quat, q: Quat) -> Quat:
    return tuple(p[i] + q[i] for i in range(4))


def scale(c: s.Expr, q: Quat) -> Quat:
    return tuple(c * x for x in q)


def sub(p: Quat, q: Quat) -> Quat:
    return add(p, scale(-1, q))


def mul(p: Quat, q: Quat) -> Quat:
    a, b, c, d = p
    e, f, g, h = q
    return (a*e-b*f-c*g-d*h, a*f+b*e+c*h-d*g,
            a*g-b*h+c*e+d*f, a*h+b*g-c*f+d*e)


def conj(q: Quat) -> Quat:
    return (q[0], -q[1], -q[2], -q[3])


def norm2(q: Quat) -> s.Expr:
    return sum(x*x for x in q)


def inv(q: Quat) -> Quat:
    return scale(1/norm2(q), conj(q))


def bracket(p: Quat, q: Quat) -> Quat:
    return sub(mul(p, q), mul(q, p))


def power(q: Quat, n: int) -> Quat:
    out = ONE
    for _ in range(n):
        out = mul(out, q)
        out = tuple(s.expand(x) for x in out)
    return out


def equal_expr(a: s.Expr, b: s.Expr) -> None:
    difference = s.cancel(s.expand(a-b))
    if difference != 0:
        difference = s.simplify(difference)
    if difference != 0:
        raise AssertionError(f"Nonzero difference: {difference}")


def equal_q(p: Quat, q: Quat) -> None:
    for a, b in zip(p, q):
        equal_expr(a, b)


def rho(q: Quat) -> s.Matrix:
    a, b, c, d = q
    return s.Matrix([[a+s.I*b, c+s.I*d], [-c+s.I*d, a-s.I*b]])


def trunc(q: Quat, n: int) -> Quat:
    """Retain powers t^0 through t^n in polynomial coordinates."""
    out = []
    for x in q:
        p = s.Poly(s.expand(x), t)
        out.append(s.Add(*(c*t**m[0] for m, c in p.terms() if m[0] <= n)))
    return tuple(out)


def tmul(p: Quat, q: Quat, n: int) -> Quat:
    return trunc(mul(p, q), n)


def exp_trunc(x: Quat, n: int) -> Quat:
    equal_q(tuple(s.expand(v).coeff(t, 0) for v in x), Z)
    term = ONE
    ans = ONE
    for k in range(1, n+1):
        term = tmul(term, x, n)
        ans = add(ans, scale(1/s.factorial(k), term))
    return trunc(ans, n)


def log1p_trunc(x: Quat, n: int) -> Quat:
    equal_q(tuple(s.expand(v).coeff(t, 0) for v in x), Z)
    term = ONE
    ans = Z
    for k in range(1, n+1):
        term = tmul(term, x, n)
        ans = add(ans, scale(s.Rational((-1)**(k+1), k), term))
    return trunc(ans, n)


def check(name: str, body: Callable[[], None]) -> None:
    try:
        body()
    except Exception as exc:
        records.append({"name": name, "passed": False, "error": str(exc)})
        raise
    records.append({"name": name, "passed": True})
    print(f"PASS {name}", flush=True)


def run_checks() -> None:
    a, b, c, d, e, f, g, h = s.symbols("a b c d e f g h", real=True)
    p: Quat = (a, b, c, d)
    q: Quat = (e, f, g, h)
    r: Quat = tuple(s.symbols("r0:4", real=True))

    def basis() -> None:
        for v in (I, J, K):
            equal_q(mul(v, v), scale(-1, ONE))
        for u, v, w in ((I, J, K), (J, K, I), (K, I, J)):
            equal_q(mul(u, v), w)
            equal_q(mul(v, u), scale(-1, w))
    check("Hamilton basis and multiplication orientation", basis)
    check("Generic associativity in twelve scalar variables", lambda: equal_q(mul(mul(p,q),r), mul(p,mul(q,r))))
    check("Conjugation reverses a generic product", lambda: equal_q(conj(mul(p,q)), mul(conj(q),conj(p))))
    check("Generic norm-square multiplicativity", lambda: equal_expr(norm2(mul(p,q)),norm2(p)*norm2(q)))
    check("Generic two-sided inverse (rational identity)", lambda: (equal_q(mul(p,inv(p)),ONE),equal_q(mul(inv(p),p),ONE)))
    check("Commutator is twice the vector cross product", lambda: equal_q(bracket(p,q),(0,2*(c*h-d*g),2*(d*f-b*h),2*(b*g-c*f))))
    check("Complex matrix representation is multiplicative", lambda: [equal_expr(x,y) for x,y in zip(rho(mul(p,q)),rho(p)*rho(q))])
    check("Complex matrix determinant is quaternion norm square", lambda: equal_expr(rho(p).det(), norm2(p)))
    check("Conjugation becomes complex matrix adjoint", lambda: [equal_expr(x,y) for x,y in zip(rho(conj(p)),rho(p).conjugate().T)])

    def rodrigues() -> None:
        v = s.Matrix([e,f,g]); u = s.Matrix([b,c,d])
        expected = (a*a-u.dot(u))*v+2*u.dot(v)*u+2*a*u.cross(v)
        equal_q(mul(mul(p,(0,e,f,g)),conj(p)), (0,*expected))
    check("Unnormalized Rodrigues conjugation identity", rodrigues)
    den = 1+b*b+c*c+d*d
    stereo: Quat = ((1-b*b-c*c-d*d)/den,2*b/den,2*c/den,2*d/den)
    check("Stereographic chart has exact unit norm", lambda: equal_expr(norm2(stereo),1))

    L = s.Matrix.hstack(*(s.Matrix(add(mul(p,u),mul(u,p))) for u in (ONE,I,J,K)))
    check("Full square-map Jacobian determinant", lambda: equal_expr(L.det(),16*a*a*norm2(p)))

    def sylvester_inverse() -> None:
        p0: Quat = (a,b,0,0)
        wpar: Quat = (e,f,0,0); wperp: Quat = (0,0,g,h)
        candidate = add(mul(inv(scale(2,p0)),wpar), scale(1/(2*a),wperp))
        equal_q(add(mul(p0,candidate),mul(candidate,p0)),q)
    check("Parallel/perpendicular inverse of square linearization", sylvester_inverse)

    def camshaft() -> None:
        def P(x: Quat) -> Quat:
            return add(sub(mul(x,x),mul(x,add(I,J))),K)
        equal_q(P(I),Z)
        equal_q(P(J),scale(2,K))
    check("One-sided factors: i is a root, j is not",camshaft)
    check("Central norm polynomial of (X-i)*(X-j)",lambda: equal_expr(norm2((t*t,-t,-t,1)),(t*t+1)**2))
    check("No-root interspersed-coefficient example",lambda: equal_q(add(add(p,mul(mul(I,p),I)),ONE),(1,0,2*c,2*d)))

    x = add(add(scale(t,I),scale(t*t,J)),scale(t**3,K))
    check("log(exp(x)) equals x through degree six",lambda: equal_q(log1p_trunc(sub(exp_trunc(x,6),ONE),6),trunc(x,6)))
    check("exp(log(1+x)) equals 1+x through degree six",lambda: equal_q(exp_trunc(log1p_trunc(x,6),6),trunc(add(ONE,x),6)))

    def bch() -> None:
        x = scale(t,add(I,scale(2,J)))
        y = scale(t,add(J,scale(3,K)))
        actual = log1p_trunc(sub(tmul(exp_trunc(x,4),exp_trunc(y,4),4),ONE),4)
        expected = add(add(x,y),scale(s.Rational(1,2),bracket(x,y)))
        expected = add(expected,scale(s.Rational(1,12),bracket(x,bracket(x,y))))
        expected = add(expected,scale(s.Rational(1,12),bracket(y,bracket(y,x))))
        expected = sub(expected,scale(s.Rational(1,24),bracket(y,bracket(x,bracket(x,y)))))
        equal_q(actual,trunc(expected,4))
    check("Noncommuting BCH formula through degree four",bch)

    def adjoint() -> None:
        n=5; x=add(scale(t,I),scale(t*t,J)); q0=add(ONE,K)
        actual=tmul(tmul(exp_trunc(x,n),q0,n),exp_trunc(scale(-1,x),n),n)
        term=q0; expected=q0
        for k in range(1,n+1):
            term=trunc(bracket(x,term),n)
            expected=add(expected,scale(1/s.factorial(k),term))
        equal_q(actual,trunc(expected,n))
    check("Adjoint exponential through degree five",adjoint)

    def group_commutator() -> None:
        n=3; x=scale(t,I); y=scale(t*t,J)
        u=exp_trunc(x,n);v=exp_trunc(y,n)
        actual=tmul(tmul(tmul(u,v,n),exp_trunc(scale(-1,x),n),n),exp_trunc(scale(-1,y),n),n)
        equal_q(actual,add(ONE,scale(2*t**3,K)))
    check("Graded group commutator leading term 2*t^3*k",group_commutator)

    def displaced_square_root() -> None:
        q0=add(ONE,I); n=7
        def linv(w: Quat) -> Quat:
            return add(mul(inv(scale(2,q0)),(w[0],w[1],0,0)),scale(s.Rational(1,2),(0,0,w[2],w[3])))
        coefficients=[Z]
        for k in range(1,n+1):
            residual=J if k==1 else Z
            for j in range(1,k):
                residual=sub(residual,mul(coefficients[j],coefficients[k-j]))
            coefficients.append(linv(residual))
        equal_q(coefficients[1],scale(s.Rational(1,2),J))
        equal_q(coefficients[2],scale(s.Rational(1,16),sub(ONE,I)))
        equal_q(coefficients[3],scale(-s.Rational(1,32),J))
        root=q0
        for k in range(1,n+1):
            root=add(root,scale(t**k,coefficients[k]))
        equal_q(trunc(mul(root,root),n),add(mul(q0,q0),scale(t,J)))
    check("Noncommuting displaced square root through degree seven",displaced_square_root)

    def radial_jacobian() -> None:
        theta,R,E=s.symbols("theta R E",real=True,nonzero=True)
        cc=s.cos(theta);ss=s.sin(theta)
        mat=E*s.Matrix([[cc,-ss,0,0],[ss,cc,0,0],[0,0,ss/R,0],[0,0,0,ss/R]])
        equal_expr(s.trigsimp(mat.det()),E**4*(ss/R)**2)
    check("Radial exponential differential determinant",radial_jacobian)

    for n in range(8):
        def fueter_check(n: int = n) -> None:
            coords=(a,b,c,d)
            poly=power(p,n)
            lap=tuple(s.expand(sum(s.diff(v,x,2) for x in coords)) for v in poly)
            result=Z
            for unit,var in zip((ONE,I,J,K),coords):
                result=add(result,mul(unit,tuple(s.diff(v,var) for v in lap)))
            equal_q(result,Z)
        check(f"Fueter-Laplacian identity for q^{n}",fueter_check)


def main() -> int:
    error = None
    try:
        run_checks()
    except Exception as exc:
        error = str(exc)
    passed=sum(row["passed"] for row in records)
    payload={
        "description":"Exact finite algebra and truncated-series checks, not formal theorem verification",
        "sympy_version":s.__version__,
        "python_version":sys.version.split()[0],
        "checks":records,
        "passed":passed,
        "total":len(records),
        "all_passed":error is None,
    }
    if error is not None:
        payload["error"]=error
    destination=Path(__file__).resolve().with_name("verification_results.json")
    destination.write_text(json.dumps(payload,indent=2)+"\n",encoding="utf-8")
    print(f"\n{passed}/{len(records)} checks passed. Results: {destination}")
    if error is not None:
        print(error,file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
