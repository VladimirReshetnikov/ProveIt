#!/usr/bin/env python3
"""Exact finite checks for Surcomplex Polynomial Algebra.

Requires Python >= 3.10 and SymPy.  No network access or floating-point
root approximations are used.  The symbol t is a formal indeterminate;
its lowest rational power is interpreted as the valuation in the examples.
These checks are not a formal verification of the general theorems.
"""
from __future__ import annotations

import itertools
import platform
from pathlib import Path
from typing import Callable, Sequence

import sympy as sp

REPORT = Path(__file__).resolve().with_name("verification_report.txt")
LINES: list[str] = []
COUNT = 0


def record(message: str) -> None:
    LINES.append(message)
    print(message, flush=True)


def check(name: str, condition: bool) -> None:
    global COUNT
    if not bool(condition):
        record(f"FAIL: {name}")
        raise AssertionError(name)
    COUNT += 1
    record(f"PASS {COUNT:03d}: {name}")


def zero(expr: sp.Expr) -> bool:
    return sp.cancel(sp.expand(expr)) == 0


def matrix_zero(matrix: sp.MatrixBase) -> bool:
    return all(zero(x) for x in matrix)


def valuation(expr: sp.Expr, t: sp.Symbol) -> sp.Expr:
    """Lowest t-degree of a nonzero rational function, with v(0)=oo."""
    expr = sp.cancel(expr)
    if expr == 0:
        return sp.oo
    numerator, denominator = sp.fraction(expr)
    pn, pd = sp.Poly(numerator, t), sp.Poly(denominator, t)
    return min(m[0] for m, _ in pn.terms()) - min(m[0] for m, _ in pd.terms())


def initial_polynomial(
    poly: sp.Expr, z: sp.Symbol, center: sp.Expr, gamma: int,
    t: sp.Symbol, X: sp.Symbol
) -> tuple[sp.Expr, sp.Expr]:
    transformed = sp.Poly(sp.expand(poly.subs(z, center + t**gamma * X)), X)
    g = min(valuation(c, t) for c in transformed.all_coeffs() if c != 0)
    initial = sum(
        sp.limit(c * t**(-g), t, 0) * X**monom[0]
        for monom, c in transformed.terms()
    )
    return g, sp.expand(initial)


def univariate_checks() -> None:
    t, z, X, s = sp.symbols("t z X s")
    record("\nUNIVARIATE VALUATIONS, EXPANSIONS, AND COLLISIONS")
    P = z**3 - t**(-2)*z + t**3
    check("cubic initial polynomial at gamma=5 is 1-X",
          initial_polynomial(P, z, 0, 5, t, X) == (3, 1-X))
    check("cubic initial polynomial at gamma=-1 is X^3-X",
          initial_polynomial(P, z, 0, -1, t, X) == (-3, X**3-X))
    small = t**5 + t**17 + 3*t**29 + 12*t**41
    check("small cubic root truncation has residual valuation 51",
          valuation(P.subs(z, small), t) == 51)
    for sign in [-1, 1]:
        large = sign/t - t**5/2
        check(f"large cubic root sign={sign}: residual valuation 9",
              valuation(P.subs(z, large), t) == 9)
    roots = [sp.Integer(0), t**3, t, t+t**2]
    quartic = sp.prod(z-r for r in roots)
    pair_depths = [valuation(roots[i]-roots[j], t)
                   for i in range(4) for j in range(i+1, 4)]
    check("quartic pair separation valuations are [3,1,1,1,1,2]",
          pair_depths == [3, 1, 1, 1, 1, 2])
    deriv_depths = [valuation(sp.diff(quartic,z).subs(z,r),t) for r in roots]
    neighbor_depths = [max(valuation(r-rj,t) for j,rj in enumerate(roots) if j!=i)
                       for i,r in enumerate(roots)]
    check("quartic derivative depths are [5,5,4,4]", deriv_depths == [5,5,4,4])
    check("quartic nearest-neighbor depths are [3,3,2,2]", neighbor_depths == [3,3,2,2])
    check("quartic tree precision threshold is 8",
          max(d+n for d,n in zip(deriv_depths,neighbor_depths)) == 8)
    check("quartic discriminant valuation is 18",
          valuation(sp.discriminant(quartic,z),t) == 18)
    _, I = initial_polynomial(quartic,z,0,1,t,X)
    check("quartic parent initial polynomial is X^2(X-1)^2", zero(I-X**2*(X-1)**2))
    _, Ip = initial_polynomial(sp.diff(quartic,z),z,0,1,t,X)
    check("initial derivative equals derivative of initial polynomial", zero(Ip-sp.diff(I,X)))
    for center,gamma in [(0,3),(t,2)]:
        _, child = initial_polynomial(quartic,z,center,gamma,t,X)
        _, child_deriv = initial_polynomial(sp.diff(quartic,z),z,center,gamma,t,X)
        check(f"child at center={center}, gamma={gamma} has 2 polynomial roots",
              sp.degree(child,X) == 2)
        check(f"child at center={center}, gamma={gamma} has critical residue 1/2",
              sp.degree(child_deriv,X) == 1 and zero(child_deriv.subs(X,sp.Rational(1,2))))
    shifts = [t**4,-t**4,t**5,-t**5]
    for i,(r,h) in enumerate(zip(roots,shifts),1):
        residual = sp.expand((quartic+t**9).subs(z,r+h))
        check(f"quartic perturbed root {i}: leading shift cancels exponent 9",
              valuation(residual,t) > 9)
    check("quadratic sharpness collision at precision 2delta (delta=3)",
          zero(z*(z-t**3)+t**6/4-(z-t**3/2)**2))
    catalan = t+t**2+2*t**3+5*t**4+14*t**5
    check("high-rank example coefficient recursion through t^5",
          valuation(catalan**2-catalan+t,t) == 6)

    # This is a polynomial parameter s, not an attempted field map t -> 0.
    Ps = (z*z-s*s)**2
    for k in range(11):
        H = z**k
        lam = sp.Poly(sp.rem(H,Ps,z),z).coeff_monomial(z**3)
        residue = (sp.diff(H,z).subs(z,s)+sp.diff(H,z).subs(z,-s))/(4*s**2)
        residue += (H.subs(z,-s)-H.subs(z,s))/(4*s**3)
        check(f"quartic double-pole residue formula on z^{k}",zero(lam-residue))
    G = sp.Matrix(4,4,lambda i,j: sp.Poly(sp.rem(z**(i+j),Ps,z),z).coeff_monomial(z**3))
    check("quartic collision residue Gram determinant is 1",zero(G.det()-1))
    for k in range(8):
        H = z**k
        lam0 = sp.Poly(sp.rem(H,z**4,z),z).coeff_monomial(z**3)
        check(f"length-four specialization matches third derivative on z^{k}",
              zero(lam0-sp.diff(H,z,3).subs(z,0)/6))


def quotient_checks(
    name: str, variables: Sequence[sp.Symbol], degrees: Sequence[int],
    equations: Sequence[sp.Expr], coefficient_symbols: Sequence[sp.Symbol] = ()
) -> None:
    """Compare exact Groebner normal forms, matrices, and divided differences."""
    record(f"\nFINITE QUOTIENT: {name}")
    xs = tuple(variables)
    ys = tuple(sp.Symbol(f"_Y_{name}_{i}") for i in range(len(xs)))
    domain = sp.QQ.frac_field(*coefficient_symbols) if coefficient_symbols else sp.QQ
    gb = sp.groebner(equations,*xs,order="grlex",domain=domain)
    exponents = list(itertools.product(*(range(d) for d in degrees)))
    monomials = [sp.prod(x**e for x,e in zip(xs,a)) for a in exponents]
    index = {a:i for i,a in enumerate(exponents)}
    dimension = len(monomials)
    top = tuple(d-1 for d in degrees)

    def nf(H: sp.Expr) -> sp.Expr:
        return sp.expand(gb.reduce(sp.expand(H))[1])

    def vector(H: sp.Expr) -> sp.Matrix:
        result = [sp.Integer(0)]*dimension
        for a,c in sp.Poly(nf(H),*xs).terms():
            if a not in index:
                raise AssertionError(f"Nonrectangular remainder {a} in {name}")
            result[index[a]] = c
        return sp.Matrix(result)

    def lam(H: sp.Expr) -> sp.Expr:
        return sp.Poly(nf(H),*xs).coeff_monomial(sp.prod(x**a for x,a in zip(xs,top)))

    def mult(H: sp.Expr) -> sp.Matrix:
        return sp.Matrix.hstack(*(vector(H*b) for b in monomials))

    check(f"{name}: every rectangular monomial is reduced",all(zero(nf(b)-b) for b in monomials))
    W = [mult(x) for x in xs]
    for i in range(len(xs)):
        for j in range(i):
            check(f"{name}: coordinate matrices {i},{j} commute",matrix_zero(W[i]*W[j]-W[j]*W[i]))
    for i,F in enumerate(equations):
        check(f"{name}: defining equation {i+1} vanishes as multiplication matrix",matrix_zero(mult(F)))
    gram = sp.Matrix(dimension,dimension,lambda i,j:lam(monomials[i]*monomials[j]))
    perm = [index[tuple(d-1-a for d,a in zip(degrees,alpha))] for alpha in exponents]
    inversions = sum(perm[i]>perm[j] for i in range(dimension) for j in range(i+1,dimension))
    sign = (-1)**inversions
    check(f"{name}: residue Gram determinant is {sign}",zero(gram.det(method="domain-ge")-sign))
    D = sp.zeros(len(xs))
    for i,F in enumerate(equations):
        for j in range(len(xs)):
            earlier = {xs[k]:ys[k] for k in range(j)}
            later = {xs[k]:ys[k] for k in range(j+1)}
            D[i,j] = sp.cancel((F.xreplace(earlier)-F.xreplace(later))/(xs[j]-ys[j]))
    delta = sp.expand(D.det())
    jac = sp.det(sp.Matrix([[sp.diff(F,x) for x in xs] for F in equations]))
    check(f"{name}: Bezoutian diagonal is the Jacobian",zero(delta.xreplace(dict(zip(ys,xs)))-jac))

    # Compute its tensor coefficients by independent normal forms in each tuple.
    tensor = sp.zeros(dimension)
    for powers,c in sp.Poly(delta,*(xs+ys)).terms():
        Xmon = sp.prod(x**a for x,a in zip(xs,powers[:len(xs)]))
        Ymon_as_X = sp.prod(x**a for x,a in zip(xs,powers[len(xs):]))
        tensor += c*vector(Xmon)*vector(Ymon_as_X).T
    check(f"{name}: Bezoutian coefficient matrix is inverse residue Gram matrix",
          matrix_zero(gram*tensor-sp.eye(dimension)))
    check(f"{name}: reduced Bezoutian tensor is symmetric",matrix_zero(tensor-tensor.T))
    for i,b in enumerate(monomials):
        check(f"{name}: Jacobian trace identity on basis index {i}",zero(sp.trace(mult(b))-lam(jac*b)))

    # Trace Gram = residue Gram times multiplication by the Jacobian.
    TG = sp.Matrix(dimension,dimension,lambda i,j:sp.trace(mult(monomials[i]*monomials[j])))
    check(f"{name}: full trace/residue matrix identity",matrix_zero(TG-gram*mult(jac)))

    if name == "symbolic_six":
        x,y=xs
        a,b,c,d=coefficient_symbols
        # itertools order here is exactly (1,y,y^2,x,xy,xy^2).
        dual=[x*y*y-a*c,x*y,x,y*y,y,sp.Integer(1)]
        check("symbolic six: displayed dual basis",
              all(zero(lam(u*v)-(1 if i==j else 0))
                  for i,u in enumerate(monomials) for j,v in enumerate(dual)))
        eliminant = y**6-2*d*y**3-a*c*c*y+d*d-b*c*c
        check("symbolic six: degree-six elimination identity",
              zero(c*c*equations[0].subs(x,(y**3-d)/c)-eliminant))


def six_root_weights() -> None:
    record("\nSIX-POINT INFINITESIMAL SPLITTING")
    # Write t=q^5 to keep all exponents integral; q is an exact formal symbol.
    q,zeta=sp.symbols("q zeta")
    x0,y0=q**4*zeta**3,q**3*zeta
    def reduce_zeta(expr:sp.Expr)->sp.Expr:
        return sp.rem(sp.expand(expr),zeta**5-1,zeta)
    check("six nonzero branches satisfy x^2-ty=0",zero(reduce_zeta(x0*x0-q**5*y0)))
    check("six nonzero branches satisfy y^3-tx=0",zero(reduce_zeta(y0**3-q**5*x0)))
    check("Jacobian at each nonzero branch is 5t^2",zero(reduce_zeta(6*x0*y0*y0-q**10)-5*q**10))
    for ax,ay in itertools.product(range(2),range(3)):
        exp=3*ax+ay
        root_sum = 5*q**(4*ax+3*ay) if exp%5==0 else sp.Integer(0)
        origin_value = 1 if ax==ay==0 else 0
        weighted = -origin_value/q**10+root_sum/(5*q**10)
        expected = 1 if (ax,ay)==(1,2) else 0
        check(f"six-point residue weights on x^{ax}y^{ay}",zero(weighted-expected))


def main() -> None:
    record("SURCOMPLEX POLYNOMIAL ALGEBRA -- EXACT FINITE VERIFICATION")
    record(f"Python {platform.python_version()}; SymPy {sp.__version__}")
    record("No floating point, no numerical root solvers, no network requests.")
    univariate_checks()
    x,y,z=sp.symbols("x y z")
    a,b,c,d=sp.symbols("a b c d")
    quotient_checks("symbolic_six",(x,y),(2,3),(x*x-a*y-b,y**3-c*x-d),(a,b,c,d))
    quotient_checks("numeric_four",(x,y),(2,2),(x*x+2*x-3*y+1,y*y+x+4*y-2))
    quotient_checks("numeric_six",(x,y),(3,2),(x**3+x*y+2*y*y-3*x+1,y*y-2*x+y-1))
    quotient_checks("numeric_eight",(x,y,z),(2,2,2),
                    (x*x+y-z+1,y*y+2*x+z-1,z*z-x+3*y+2))
    six_root_weights()
    record(f"\nALL {COUNT} EXACT CHECKS PASSED.")
    record("Scope: finite examples and displayed symbolic identities only.")
    record("Not verified by this script: arbitrary Hahn supports, transfinite recursion,")
    record("class-set foundations, real-closed transfer, or all-ring universal proofs.")


if __name__ == "__main__":
    try:
        main()
    except Exception as exc:
        record(f"\nVERIFICATION ABORTED: {type(exc).__name__}: {exc}")
        raise
    finally:
        REPORT.write_text("\n".join(LINES)+"\n",encoding="utf-8")
