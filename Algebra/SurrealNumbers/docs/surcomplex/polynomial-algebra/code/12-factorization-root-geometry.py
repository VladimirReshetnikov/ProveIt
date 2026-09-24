#!/usr/bin/env python3
"""Exact finite checks for Surcomplex Polynomial Algebra.

Requires Python 3.10+ and SymPy.  This is NOT a proof assistant certificate
and does not implement arbitrary surreal numbers or arbitrary Hahn supports.
Run: python verify_examples.py [--output verification.txt]
"""
from __future__ import annotations

import argparse
from pathlib import Path
import platform
import time

import sympy as sp

X, U, T, Y = sp.symbols("X U t Y")
CHECKS = 0
MESSAGES: list[str] = []


def require(condition: object, description: str) -> None:
    """Raise a descriptive error even when Python is run with -O."""
    global CHECKS
    if condition is not True and condition != sp.true:
        raise AssertionError(description)
    CHECKS += 1


def equal(a: sp.Expr, b: sp.Expr, description: str) -> None:
    require(sp.cancel(a - b) == 0, description)


def matrix_equal(a: sp.MatrixBase, b: sp.MatrixBase, description: str) -> None:
    require(a.shape == b.shape, description + " (shape)")
    for i in range(a.rows):
        for j in range(a.cols):
            equal(a[i, j], b[i, j], f"{description} ({i}, {j})")


def valuation(expr: sp.Expr) -> sp.Expr:
    """t-adic valuation of a rational function in t, with symbolic constants."""
    expr = sp.cancel(expr)
    if expr == 0:
        return sp.oo
    numerator, denominator = sp.fraction(expr)
    pn, pd = sp.Poly(numerator, T), sp.Poly(denominator, T)
    return sp.Integer(min(k[0] for k in pn.monoms()) - min(k[0] for k in pd.monoms()))


def leading_coefficient(expr: sp.Expr) -> sp.Expr:
    if sp.cancel(expr) == 0:
        raise ValueError("Zero has no leading coefficient")
    numerator, denominator = sp.fraction(sp.cancel(expr))
    pn, pd = sp.Poly(numerator, T), sp.Poly(denominator, T)
    en, ed = min(k[0] for k in pn.monoms()), min(k[0] for k in pd.monoms())
    return sp.cancel(pn.nth(en) / pd.nth(ed))


def reduction(poly: sp.Expr, center: sp.Expr, scale: int) -> tuple[sp.Expr, sp.Expr]:
    """Return weight and reduction in U for integer t-scales."""
    translated = sp.Poly(sp.expand(poly.subs(X, center + U)), U)
    items = [(j, translated.nth(j)) for j in range(translated.degree() + 1)
             if translated.nth(j) != 0]
    weight = min(valuation(c) + j * scale for j, c in items)
    red = sum(leading_coefficient(c) * U**j for j, c in items
              if valuation(c) + j * scale == weight)
    return sp.sympify(weight), sp.expand(red)


def rem(poly: sp.Expr, modulus: sp.Expr) -> sp.Expr:
    return sp.rem(sp.expand(poly), modulus, X)


def coefficient_vector(poly: sp.Expr, n: int) -> sp.Matrix:
    p = sp.Poly(sp.expand(poly), X)
    return sp.Matrix([p.nth(i) for i in range(n)])


def multiplication_matrix(h: sp.Expr, modulus: sp.Expr) -> sp.Matrix:
    n = sp.degree(modulus, X)
    return sp.Matrix.hstack(*(coefficient_vector(rem(h * X**j, modulus), n)
                              for j in range(n)))


def residue(h: sp.Expr, modulus: sp.Expr) -> sp.Expr:
    return sp.Poly(rem(h, modulus), X).nth(sp.degree(modulus, X) - 1)


def generic_residue_checks() -> None:
    for n in range(1, 7):
        coeffs = sp.symbols(f"a0:{n}")
        p = X**n + sum(coeffs[j] * X**j for j in range(n))
        pn = [*coeffs, sp.Integer(1)]
        G = sp.Matrix(n, n, lambda i, j: residue(X**(i + j), p))
        duals = [sum(pn[k] * X**(k - 1 - i) for k in range(i + 1, n + 1))
                 for i in range(n)]
        inverse = sp.Matrix.hstack(*(coefficient_vector(d, n) for d in duals))
        matrix_equal(G * inverse, sp.eye(n), f"generic degree {n} residue inverse")
        equal(G.det(method="domain-ge"), (-1)**(n * (n - 1) // 2),
              f"generic degree {n} residue determinant")
        equal(sum(X**i * duals[i] for i in range(n)), sp.diff(p, X),
              f"generic degree {n} Euler element")
        bezout = sp.div(p - p.subs(X, U), X - U, X)[0]
        equal(bezout, sum(duals[i] * U**i for i in range(n)),
              f"generic degree {n} Bezout kernel")
        MX = multiplication_matrix(X, p)
        power = sp.eye(n)
        sums = [sp.Integer(n)]
        for k in range(1, 2 * n + 1):
            power = (power * MX).applyfunc(sp.expand)
            sums.append(sp.expand(sp.trace(power)))
            if k <= n:
                terms = sums[k] + sum(pn[n-j] * sums[k-j] for j in range(1, k)) + k * pn[n-k]
            else:
                terms = sums[k] + sum(pn[n-j] * sums[k-j] for j in range(1, n + 1))
            equal(terms, 0, f"generic degree {n} Newton identity k={k}")
        for j in range(n):
            equal(sums[j], residue(sp.diff(p, X) * X**j, p),
                  f"generic degree {n} trace identity basis index {j}")
        q = X**2 + 2 * X + 3
        norm_matrix = MX * MX + 2 * MX + 3 * sp.eye(n)
        equal(norm_matrix.det(method="domain-ge"), sp.resultant(p, q, X),
              f"generic degree {n} norm-resultant identity")
        if n <= 4:
            trace_gram = sp.Matrix(n, n, lambda i, j: sums[i+j])
            equal(trace_gram.det(method="domain-ge"), sp.discriminant(p, X),
                  f"generic degree {n} trace discriminant")
    MESSAGES.append("PASS: generic monic degrees 1..6: residue dual bases, inverse Gram matrices, determinants, Bezout kernels, Euler/derivative identities, trace identities on every basis vector, Newton sums through 2n, and norms of X^2+2X+3. Generic trace-discriminant determinants checked for degrees 1..4.")


def reduction_checks() -> None:
    roots = [T**-2, sp.Integer(1), T + T**3, T - T**4, T**3, sp.Integer(0), sp.Integer(0)]
    p = sp.expand(sp.prod(X - a for a in roots))
    cases = 0
    for center in (sp.Integer(0), T, sp.Integer(1)):
        for scale in range(-3, 6):
            w, R = reduction(p, center, scale)
            distances = [valuation(a - center) for a in roots]
            closed = sum(int(bool(d >= scale)) for d in distances)
            opened = sum(int(bool(d > scale)) for d in distances)
            poly_R = sp.Poly(R, U)
            equal(poly_R.degree(), closed, "closed-ball root count")
            equal(min(k[0] for k in poly_R.monoms()), opened, "open-ball root count")
            equal(w, sum(min(sp.Integer(scale), d) for d in distances), "Gauss root weight")
            residues = [sp.Integer(0) if d > scale else leading_coefficient(a-center)
                        for a, d in zip(roots, distances) if d >= scale]
            equal(R / poly_R.LC(), sp.prod(U-c for c in residues), "all residue multiplicities")
            if closed > 0:
                wp, Rp = reduction(sp.diff(p, X), center, scale)
                equal(wp, w-scale, "derivative normalization weight")
                equal(Rp, sp.diff(R, U), "derivative reduction")
                equal(sp.degree(Rp, U), closed-1, "closed critical count")
                if opened > 0:
                    equal(min(k[0] for k in sp.Poly(Rp, U).monoms()), opened-1,
                          "open critical count")
            cases += 1
    MESSAGES.append(f"PASS: degree-7 factored polynomial, including infinite, finite, infinitesimal, and repeated roots: {cases} center/scale charts (centers 0,t,1; integer scales -3..5). Exact weights, closed/open counts, all residue multiplicities, and derivative reductions checked.")


def named_examples() -> None:
    p = X**3 - T**2 * X - T**5
    equal(reduction(p, 0, 1)[1], U**3-U, "cubic reduction scale 1")
    equal(reduction(p, 0, 3)[1], -U-1, "cubic reduction scale 3")
    plus = T + T**3/2 - 3*T**5/8
    minus = -T + T**3/2 + 3*T**5/8
    small = -T**3 - T**7
    require(valuation(p.subs(X, plus)) >= 9, "cubic positive root truncation")
    require(valuation(p.subs(X, minus)) >= 9, "cubic negative root truncation")
    require(valuation(p.subs(X, small)) >= 13, "cubic small root truncation")
    equal(sp.diff(p, X).subs(X, T/sp.sqrt(3)), 0, "cubic critical plus")
    equal(sp.diff(p, X).subs(X, -T/sp.sqrt(3)), 0, "cubic critical minus")

    roots = [T, T+T**3, -T, sp.Integer(1)]
    quartic = sp.expand(sp.prod(X-a for a in roots))
    derivative = sp.diff(quartic, X)
    sigmas = [valuation(derivative.subs(X, a)) for a in roots]
    deltas = [max(valuation(a-b) for j, b in enumerate(roots) if j != i)
              for i, a in enumerate(roots)]
    require(sigmas == [4,4,2,0], "quartic derivative weights")
    require(deltas == [3,3,1,0], "quartic separation scales")
    equal(max(a+b for a,b in zip(sigmas,deltas)), 7, "quartic root-specific threshold")
    disc = sp.discriminant(quartic, X)
    equal(valuation(disc), 10, "quartic discriminant valuation")
    equal(leading_coefficient(disc), 16, "quartic discriminant leading coefficient")
    for center, scale, expected in [(0,0,U**3*(U-1)),
                                   (0,1,-(U-1)**2*(U+1)),
                                   (T,3,-2*U*(U-1))]:
        equal(reduction(quartic, center, scale)[1], expected, "quartic branching reduction")
    shifts = [-T**4/2, T**4/2, T**6/4, -T**8]
    for a, h in zip(roots, shifts):
        newton = -T**8/derivative.subs(X,a)
        equal(valuation(newton), valuation(h), "quartic leading shift valuation")
        equal(leading_coefficient(newton), leading_coefficient(h), "quartic leading shift coefficient")
        require(valuation((quartic+T**8).subs(X,a+h)) > 8,
                "quartic first shift residual improves beyond input error")
    h = sp.Integer(3)
    p2 = X*(X-T**h)
    q2 = (X-T**h/2)**2
    equal(q2-p2, T**(2*h)/4, "quadratic boundary error")
    equal(sp.discriminant(q2, X), 0, "quadratic boundary collision")
    equal(valuation(sp.discriminant(p2, X)), 2*h, "quadratic input discriminant")
    MESSAGES.append("PASS: cubic two-scale reductions, three displayed root truncations (residual orders >=9, >=9, >=13), and exact critical points. Quartic distance/derivative data, D=10 with leading coefficient 16, T(P)=7, three branching reductions, and all four leading shifts for P+t^8. Strict-boundary quadratic collision checked at h=3.")


def hensel_checks() -> None:
    A0, B0 = X-1, X**2+1
    p = sp.expand(A0*B0 + T*(X**2+2*X+3) + T**2*(X-4))
    linear = sp.Matrix.hstack(coefficient_vector(B0,3),
                             coefficient_vector(A0,3),
                             coefficient_vector(X*A0,3))
    inverse = linear.inv()
    ac, bc = [sp.Integer(0)]*7, [sp.Integer(0)]*7
    delta = sp.Poly(sp.expand(p-A0*B0), T)
    for k in range(1,7):
        known = sum(ac[i]*bc[k-i] for i in range(1,k))
        solution = inverse*coefficient_vector(delta.nth(k)-known,3)
        ac[k] = solution[0]
        bc[k] = solution[1]+solution[2]*X
    A = A0+sum(ac[k]*T**k for k in range(1,7))
    B = B0+sum(bc[k]*T**k for k in range(1,7))
    error = sp.Poly(sp.expand(A*B-p),T)
    for k in range(7):
        equal(error.nth(k),0,f"Hensel product coefficient {k}")
    s = sp.symbols("s", nonzero=True)
    r = s*sum(sp.binomial(sp.Rational(1,2),k)*(-T/s**2)**k for k in range(6))
    error_parameter = sp.Poly(sp.expand((X-r)*(X+r)-(X**2-s**2+T)),T)
    for k in range(6):
        equal(error_parameter.nth(k),0,f"parameter Hensel coefficient {k}")
    MESSAGES.append("PASS: explicit coprime factor recursion through t^6 for (X-1)(X^2+1)+t(X^2+2X+3)+t^2(X-4). Parameter root factors of X^2-s^2+t checked through t^5 over Q(s), s nonzero.")


def crt_collision_branch_checks() -> None:
    nodes = [(T,2),(-T,3)]
    p = sp.expand(sp.prod((X-a)**m for a,m in nodes))
    idempotents: list[sp.Expr] = []
    for a,m in nodes:
        A = (X-a)**m
        quotient = sp.div(p,A,X)[0]
        C = sp.invert(quotient,A,X)
        E = rem(quotient*C,p)
        idempotents.append(E)
        equal(rem(E*E-E,p),0,"Hermite CRT idempotent")
    equal(rem(sum(idempotents)-1,p),0,"Hermite CRT identity sum")
    equal(rem(idempotents[0]*idempotents[1],p),0,"Hermite CRT orthogonality")
    jet = [1+2*(X-T),3+4*(X+T)+5*(X+T)**2]
    interpolant = rem(sum(e*j for e,j in zip(idempotents,jet)),p)
    for (a,m),target in zip(nodes,jet):
        for j in range(m):
            equal(sp.diff(interpolant-target,X,j).subs(X,a),0,"Hermite CRT jet")

    a,b=sp.symbols("a b")
    cubic=X**3-a*X-b
    G=sp.Matrix(3,3,lambda i,j:residue(X**(i+j),cubic))
    expected=sp.Matrix([[0,0,1],[0,1,0],[1,0,a]])
    matrix_equal(G,expected,"credited cubic residue matrix")
    collision=(X-2*T)*(X+T)**2
    for j in range(7):
        h=X**j
        rhs=(h.subs(X,2*T)-h.subs(X,-T))/(9*T**2)-sp.diff(h,X).subs(X,-T)/(3*T)
        equal(residue(h,sp.expand(collision)),rhs,"cubic collision residue on monomial")
    for critical in ([0],[-1,2],[0,0,1],[-2,0,1,1]):
        n=len(critical)+1
        derivative=n*sp.prod(X-c for c in critical)
        poly=sp.integrate(derivative,X)+3
        lhs=sp.discriminant(poly-Y,X)
        rhs=(-1)**(n*(n-1)//2)*n**n*sp.prod(poly.subs(X,c)-Y for c in critical)
        equal(lhs,rhs,f"degree {n} branch-value discriminant")
    MESSAGES.append("PASS: Hermite CRT with multiplicities 2 and 3 at infinitesimally separated nodes; all idempotent and jet identities. Credited cubic residue matrix and repeated-root residue formula on monomials 0..6. Branch-value discriminant formula in degrees 2..5, including repeated critical points.")


def uncertainty_checks() -> None:
    z=1+2*sp.I
    p=X**3+X+1
    weights=[sp.Integer(1),sp.Integer(2),sp.Integer(3)]
    sizes=[sp.Abs(z**j) for j in range(3)]
    S=sum(e*r for e,r in zip(weights,sizes))
    errors=[sp.simplify(-p.subs(X,z)*weights[j]*sp.conjugate(z**j)/(S*sizes[j]))
            for j in range(3)]
    equal(p.subs(X,z)+sum(errors[j]*z**j for j in range(3)),0,"modulus pseudozero witness")
    for j,e in enumerate(errors):
        require(sp.simplify(weights[j]**2-e*sp.conjugate(e)).is_nonnegative,
                "modulus pseudozero bound")
    pv=X**3-T**4*X+T**9
    zv=T**2
    bounds=[8,6,9]
    j0=min(range(3),key=lambda j:bounds[j]+valuation(zv**j))
    e=-pv.subs(X,zv)/zv**j0
    require(valuation(e)>bounds[j0],"strict valuation pseudozero coefficient witness")
    equal(pv.subs(X,zv)+e*zv**j0,0,"valuation pseudozero root witness")
    MESSAGES.append("PASS: exact modulus coefficient-phase witness at z=1+2i with three independent weights; exact one-coefficient strict valuation witness at z=t^2. These are finite samples of the proved uncertainty formulas, not universal numerical verification.")


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path,default=Path(__file__).with_name("verification.txt"))
    args=parser.parse_args()
    start=time.perf_counter()
    for test in (generic_residue_checks,reduction_checks,named_examples,
                 hensel_checks,crt_collision_branch_checks,uncertainty_checks):
        test()
        print(MESSAGES[-1],flush=True)
    report="\n".join([
        "SURCOMPLEX POLYNOMIAL ALGEBRA — EXACT FINITE CHECKS",
        f"Python {platform.python_version()}; SymPy {sp.__version__}",
        "All computations use exact rational/symbolic arithmetic; no numerical root approximation is used.",
        "",*MESSAGES,"",f"PASS: {CHECKS} assertions completed in {time.perf_counter()-start:.2f} seconds.",
        "", "LIMITATIONS",
        "These checks do not implement arbitrary surreal coefficients or arbitrary-rank Hahn fields.",
        "They do not prove transfinite summability, real-closed transfer, the general root matching theorem, or the Nullstellensatz.",
        "They are reproducible checks of finite identities and worked instances; the manuscript contains the general proofs.",""
    ])
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(report,encoding="utf-8")
    print(f"Saved {args.output}; {CHECKS} assertions passed.",flush=True)


if __name__ == "__main__":
    main()
