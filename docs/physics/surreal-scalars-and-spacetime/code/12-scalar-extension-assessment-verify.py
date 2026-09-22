#!/usr/bin/env python3
"""Exact symbolic checks accompanying article.tex.

Requires Python 3.10+ and SymPy. Run: python verify.py

These are checks of finite symbolic identities, not a formal verification of
surreal analysis, general relativity, or any physical interpretation. In
particular, this program does not implement a surreal number field.
"""
from __future__ import annotations

import sys

try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("SymPy is required. Install it with: python -m pip install sympy") from exc

CHECKS: list[str] = []


def check_zero(name: str, expression: sp.Expr) -> None:
    """Require exact symbolic zero; never accept a numerical approximation."""
    reduced = sp.simplify(expression)
    if reduced != 0:
        raise AssertionError(f"{name}: nonzero residual {reduced}")
    CHECKS.append(name)
    print(f"PASS {len(CHECKS):02d}: {name}", flush=True)


def check_true(name: str, condition: bool) -> None:
    if not condition:
        raise AssertionError(name)
    CHECKS.append(name)
    print(f"PASS {len(CHECKS):02d}: {name}", flush=True)


def independent_static_curvature(r: sp.Symbol) -> tuple[sp.Expr, sp.Expr, sp.Expr]:
    """Construct coordinate connection and Riemann tensor from the metric.

    Returns the curvature square, scalar curvature, and mixed G^t_t.
    No precomputed curvature formulas are used inside this function.
    The metric and inverse are diagonal, making the final contraction sparse.
    """
    time, theta, phi = sp.symbols("time theta phi", real=True)
    coords = (time, r, theta, phi)
    f = sp.Function("f")(r)
    diagonal = (-f, 1 / f, r**2, r**2 * sp.sin(theta)**2)
    metric = sp.diag(*diagonal)
    inverse = sp.diag(*(1 / element for element in diagonal))
    gamma: dict[tuple[int, int, int], sp.Expr] = {}
    for a in range(4):
        for b in range(4):
            for c in range(4):
                value = sum(
                    inverse[a, d] * (
                        sp.diff(metric[d, c], coords[b])
                        + sp.diff(metric[d, b], coords[c])
                        - sp.diff(metric[b, c], coords[d])
                    ) / 2
                    for d in range(4)
                )
                gamma[a, b, c] = sp.simplify(value)

    riemann: dict[tuple[int, int, int, int], sp.Expr] = {}
    for a in range(4):
        for b in range(4):
            for c in range(4):
                for d in range(4):
                    value = (
                        sp.diff(gamma[a, d, b], coords[c])
                        - sp.diff(gamma[a, c, b], coords[d])
                        + sum(
                            gamma[a, c, e] * gamma[e, d, b]
                            - gamma[a, d, e] * gamma[e, c, b]
                            for e in range(4)
                        )
                    )
                    riemann[a, b, c, d] = sp.simplify(sp.trigsimp(value))

    ricci = sp.Matrix(4, 4, lambda b, d: sp.simplify(
        sum(riemann[a, b, a, d] for a in range(4))))
    scalar = sp.simplify(sum(ricci[a, a] / diagonal[a] for a in range(4)))
    kretschmann = sp.simplify(sum(
        diagonal[a] * value**2 / (diagonal[b] * diagonal[c] * diagonal[d])
        for (a, b, c, d), value in riemann.items() if value != 0
    ))
    einstein_tt = sp.simplify(ricci[0, 0] / diagonal[0] - scalar / 2)
    return kretschmann, scalar, einstein_tt


def main() -> int:
    print("Finite symbolic verification for Surreal Scalars and Physical Singularities")
    print(f"Python {sys.version.split()[0]}; SymPy {sp.__version__}")
    print("All comparisons below are exact symbolic comparisons.\n")
    r, m, ell, u, eps = sp.symbols("r m ell u eps", positive=True)
    f = sp.Function("f")(r)

    def curvature(fn: sp.Expr) -> sp.Expr:
        return sp.diff(fn, r, 2)**2 + 4*(sp.diff(fn, r)/r)**2 + 4*((1-fn)/r**2)**2

    def scalar(fn: sp.Expr) -> sp.Expr:
        return -sp.diff(fn, r, 2)-4*sp.diff(fn, r)/r+2*(1-fn)/r**2

    k_auto, r_auto, g_tt_auto = independent_static_curvature(r)
    check_zero("independent coordinate Riemann contraction gives general K[f]", k_auto-curvature(f))
    check_zero("independent coordinate Ricci tensor gives scalar curvature", r_auto-scalar(f))
    check_zero("independent coordinate Einstein tensor gives mixed G^t_t", g_tt_auto-(r*sp.diff(f,r)+f-1)/r**2)

    schwarz = 1-2*m/r
    check_zero("Schwarzschild Kretschmann scalar", curvature(schwarz)-48*m**2/r**6)
    check_zero("Schwarzschild Ricci scalar vanishes", scalar(schwarz))
    check_zero("Schwarzschild mixed G^t_t vanishes", (r*sp.diff(schwarz,r)+schwarz-1)/r**2)
    check_zero("finite horizon curvature", curvature(schwarz).subs(r,2*m)-sp.Rational(3,4)/m**4)
    check_zero("dimensionless infinitesimal-radius curvature", (m**4*curvature(schwarz)).subs(r,m*eps)-48/eps**6)
    ef_block = sp.Matrix([[-schwarz,1],[1,0]])
    check_zero("ingoing metric radial-time block determinant", ef_block.det()+1)

    r_of_u = (sp.Rational(9,2)*m*u**2)**sp.Rational(1,3)
    check_zero("radial E=1 infall first integral", sp.diff(r_of_u,u)**2-2*m/r_of_u)
    check_zero("proper-time curvature coefficient 64/27", (48*m**2/r**6).subs(r,r_of_u)-sp.Rational(64,27)/u**4)
    check_zero("proper-time radial tide 4/(9u^2)", (2*m/r**3).subs(r,r_of_u)-sp.Rational(4,9)/u**2)
    check_zero("proper-time transverse tide -2/(9u^2)", (-m/r**3).subs(r,r_of_u)+sp.Rational(2,9)/u**2)
    a = sp.symbols("a")
    check_true("radial indicial roots", set(sp.solve(a*(a-1)-sp.Rational(4,9),a)) == {sp.Rational(4,3),sp.Rational(-1,3)})
    check_true("transverse indicial roots", set(sp.solve(a*(a-1)+sp.Rational(2,9),a)) == {sp.Rational(2,3),sp.Rational(1,3)})

    def kasner_coefficient(ps: tuple[sp.Expr, sp.Expr, sp.Expr]) -> sp.Expr:
        return 4*(sum(p**2*(p-1)**2 for p in ps)+sum(ps[j]**2*ps[k]**2 for j in range(3) for k in range(j+1,3)))

    ps = (sp.Rational(-1,3),sp.Rational(2,3),sp.Rational(2,3))
    check_zero("Kasner sum constraint",sum(ps)-1)
    check_zero("Kasner squared-sum constraint",sum(p*p for p in ps)-1)
    check_zero("Kasner curvature coefficient 64/27", kasner_coefficient(ps)-sp.Rational(64,27))
    check_zero("flat Kasner special case", kasner_coefficient((sp.Integer(1),sp.Integer(0),sp.Integer(0))))

    core = 1-2*m*r**2/(r**3+2*m*ell**2)
    check_zero("regular-core central curvature",sp.limit(curvature(core),r,0,dir="+")-24/ell**4)
    check_zero("regular-core central scalar curvature",sp.limit(scalar(core),r,0,dir="+")-12/ell**2)
    mass_fn = m*r**3/(r**3+2*m*ell**2)
    rho = sp.diff(mass_fn,r)/(4*sp.pi*r**2)
    check_zero("regular-core effective density",rho-3*m**2*ell**2/(2*sp.pi*(r**3+2*m*ell**2)**2))
    check_zero("regular-core central density",sp.limit(rho,r,0,dir="+")-3/(8*sp.pi*ell**2))
    check_zero("regular-core Einstein source identity", (r*sp.diff(core,r)+core-1)/r**2+8*sp.pi*rho)
    check_zero("regular-core expansion through r^5",sp.series(core,r,0,6).removeO()-(1-r**2/ell**2+r**5/(2*m*ell**4)))
    check_zero("infinitesimal core has infinite-order formal curvature", (24*m**4/ell**4).subs(ell,m*eps)-24/eps**4)

    x, X = sp.symbols("x X", positive=True)
    rational_core = 1-2*x**2/(x**3+2*eps**2)
    check_zero("outer rational representation",rational_core-(1-(2/x)/(1+2*eps**2/x**3)))
    check_zero("inner rational representation",rational_core-(1-(x**2/eps**2)/(1+x**3/(2*eps**2))))
    check_zero("transition-scale exact rational expression",rational_core.subs(x,eps**sp.Rational(2,3)*X)-(1-2*eps**sp.Rational(-2,3)*X**2/(X**3+2)))
    A = sp.symbols("A")
    for count in range(1,9):
        partial = sum((-A)**k for k in range(count))
        check_zero(f"geometric exact remainder, N={count}",1/(1+A)-partial-(-A)**count/(1+A))

    delta = sp.symbols("delta", positive=True)
    layer = delta**4/(delta**2+x**2)
    check_zero("boundary-layer second derivative at zero",sp.diff(layer,x,2).subs(x,0)+2)
    y = sp.symbols("y", real=True)
    check_zero("boundary-layer derivative scaling",sp.diff(layer,x).subs(x,delta*y)+2*delta*y/(1+y*y)**2)
    ell_p = sp.symbols("ell_P", positive=True)
    r_q = 48**sp.Rational(1,6)*(m*ell_p**2)**sp.Rational(1,3)
    check_zero("Planck-curvature dimensional threshold",48*m*m*ell_p**4/r_q**6-1)
    alpha,beta = sp.symbols("alpha beta",positive=True)
    check_zero("two-scale curvature exponent",48*(eps**beta)**4/(eps**alpha)**6-48*eps**(4*beta-6*alpha))

    z = sp.symbols("z",real=True)
    gaussian = sp.exp(-z*z/eps**2)/(eps*sp.sqrt(sp.pi))
    check_zero("Gaussian regulator integrates to one",sp.integrate(gaussian,(z,-sp.oo,sp.oo))-1)
    check_zero("squared Gaussian regulator divergent integral",sp.integrate(gaussian**2,(z,-sp.oo,sp.oo))-1/(eps*sp.sqrt(2*sp.pi)))
    check_zero("two-level Born probabilities normalize",1/(1+eps**2)+eps**2/(1+eps**2)-1)
    check_zero("rare-outcome ordinary limit",sp.limit(eps**2/(1+eps**2),eps,0,dir="+"))

    print(f"\nAll {len(CHECKS)} finite symbolic checks passed.")
    print("Scope: algebraic identities only; no claim of a verified surreal field,")
    print("general PDE existence, geodesic completion, or a physical singularity cure.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
