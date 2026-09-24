#!/usr/bin/env python3
"""Exact checks for the examples in surreal_numbers_black_holes.tex.

Requires Python 3.9+ and SymPy. Run:
    python verify_identities.py

These are symbolic checks of displayed identities, not formal proofs of the
article's abstract theorems, nor an implementation of surreal arithmetic.
The curvature tensor uses R^a_{bcd} = d_c Gamma^a_{bd} - d_d Gamma^a_{bc}
                                      + Gamma^a_{ce} Gamma^e_{bd}
                                      - Gamma^a_{de} Gamma^e_{bc}.
"""
from __future__ import annotations

import itertools
import sys
from functools import lru_cache
from typing import Callable, Sequence

try:
    import sympy as sp
except ImportError:
    sys.exit("SymPy is required. Install it with: python -m pip install sympy")

CHECKS: list[str] = []


def check(name: str, expression: sp.Expr, expected: sp.Expr = sp.S.Zero) -> None:
    """Fail explicitly unless exact symbolic simplification proves equality."""
    residual = sp.simplify(sp.trigsimp((expression - expected).doit()))
    if residual != 0:
        raise AssertionError(f"{name}: nonzero residual {residual}")
    CHECKS.append(name)
    print(f"PASS {len(CHECKS):02d}: {name}", flush=True)


def connection(metric: sp.Matrix, coordinates: Sequence[sp.Symbol]) -> Callable:
    inverse = metric.inv()
    dimension = len(coordinates)

    @lru_cache(None)
    def gamma(a: int, b: int, c: int) -> sp.Expr:
        return sp.simplify(sum(
            inverse[a, e] * (
                sp.diff(metric[e, c], coordinates[b])
                + sp.diff(metric[e, b], coordinates[c])
                - sp.diff(metric[b, c], coordinates[e])
            ) for e in range(dimension)
        ) / 2)
    return gamma


def curvature(gamma: Callable, coordinates: Sequence[sp.Symbol]) -> Callable:
    dimension = len(coordinates)

    @lru_cache(None)
    def riemann(a: int, b: int, c: int, d: int) -> sp.Expr:
        if c == d:
            return sp.S.Zero
        if c > d:
            return -riemann(a, b, d, c)
        expression = (
            sp.diff(gamma(a, b, d), coordinates[c])
            - sp.diff(gamma(a, b, c), coordinates[d])
            + sum(gamma(a, c, e) * gamma(e, b, d)
                  - gamma(a, d, e) * gamma(e, b, c)
                  for e in range(dimension))
        )
        return sp.simplify(sp.trigsimp(expression))
    return riemann


def main() -> None:
    print(f"Python {sys.version.split()[0]}; SymPy {sp.__version__}")
    print("Exact symbolic identity checks; not a formal verification of the article.\n")
    time, r, theta, phi = sp.symbols("time r theta phi", real=True)
    m, ell, lp, s, epsilon = sp.symbols("m ell lp s epsilon", positive=True)
    f = sp.Function("f")(r)
    coordinates = (time, r, theta, phi)
    diagonal = (-f, 1/f, r**2, r**2 * sp.sin(theta)**2)
    gamma = connection(sp.diag(*diagonal), coordinates)
    riemann = curvature(gamma, coordinates)

    # Independent contraction of the tensor, not just the scalar formula.
    kretschmann = sp.S.Zero
    for a, b, c, d in itertools.product(range(4), repeat=4):
        component = riemann(a, b, c, d)
        if component != 0:
            kretschmann += (diagonal[a] / (diagonal[b]*diagonal[c]*diagonal[d])) * component**2
    expected_k = sp.diff(f, r, 2)**2 + 4*(sp.diff(f, r)/r)**2 + 4*((1-f)/r**2)**2
    check("generic static-spherical Riemann contraction", kretschmann, expected_k)

    schwarzschild = 1 - 2*m/r
    for b, d in itertools.product(range(4), repeat=2):
        ricci = sum(riemann(a, b, a, d) for a in range(4))
        check(f"Schwarzschild Ricci component ({b},{d})", ricci.subs(f, schwarzschild).doit())
    k_schwarz = sp.simplify(expected_k.subs(f, schwarzschild).doit())
    check("Schwarzschild Kretschmann scalar", k_schwarz, 48*m**2/r**6)
    check("horizon curvature", k_schwarz.subs(r, 2*m), sp.Rational(3,4)/m**4)
    check("ingoing Eddington-Finkelstein radial determinant", sp.Matrix([[-schwarzschild,1],[1,0]]).det(), -1)
    check("infinitesimal-radius curvature identity", k_schwarz.subs(r,m*epsilon), 48/(m**4*epsilon**6))

    radial = (sp.Rational(9,2)*m)**sp.Rational(1,3) * s**sp.Rational(2,3)
    check("radial proper-time cubic relation", radial**3, sp.Rational(9,2)*m*s**2)
    check("radial E=1 geodesic equation", sp.diff(radial,s)**2, 2*m/radial)
    check("proper-time curvature coefficient", k_schwarz.subs(r,radial), sp.Rational(64,27)/s**4)
    check("radial tidal coefficient", 2*m/radial**3, sp.Rational(4,9)/s**2)
    check("transverse tidal coefficient", -m/radial**3, -sp.Rational(2,9)/s**2)
    for p in (sp.Rational(-1,3), sp.Rational(4,3)):
        check(f"radial Jacobi power {p}", sp.diff(s**p,s,2), sp.Rational(4,9)*s**p/s**2)
    for p in (sp.Rational(1,3), sp.Rational(2,3)):
        check(f"transverse Jacobi power {p}", sp.diff(s**p,s,2), -sp.Rational(2,9)*s**p/s**2)

    def kasner_coefficient(powers: tuple) -> sp.Expr:
        return 4 * (sum(p**2*(p-1)**2 for p in powers)
                    + sum(powers[i]**2*powers[j]**2 for i in range(3) for j in range(i+1,3)))

    powers = (sp.Rational(-1,3),sp.Rational(2,3),sp.Rational(2,3))
    check("Kasner linear constraint", sum(powers), 1)
    check("Kasner quadratic constraint", sum(p*p for p in powers), 1)
    check("Schwarzschild-like Kasner coefficient", kasner_coefficient(powers), sp.Rational(64,27))
    for powers in ((1,0,0),(0,1,0),(0,0,1)):
        check(f"flat Kasner coefficient {powers}", sp.sympify(kasner_coefficient(powers)))

    mass = m*r**3/(r**3+2*m*ell**2)
    hayward = 1 - 2*m*r**2/(r**3+2*m*ell**2)
    check("Hayward mass-function identity", hayward, 1-2*mass/r)
    series = sp.series(hayward,r,0,8).removeO()
    check("Hayward central expansion", series, 1-r**2/ell**2+r**5/(2*m*ell**4))
    k_core = sp.simplify(expected_k.subs(f,hayward).doit())
    check("Hayward central curvature", sp.limit(k_core,r,0), 24/ell**4)
    density = sp.diff(mass,r)/(4*sp.pi*r**2)
    check("Hayward effective density", density, 3*m**2*ell**2/(2*sp.pi*(r**3+2*m*ell**2)**2))
    check("Hayward central density", sp.limit(density,r,0), 3/(8*sp.pi*ell**2))
    check("Hayward leading outer correction", sp.limit(r**4*(hayward-schwarzschild),r,sp.oo), 4*m**2*ell**2)

    radius_q = 48**sp.Rational(1,6) * (m*lp**2)**sp.Rational(1,3)
    check("curvature power-counting radius", 48*m**2*lp**4/radius_q**6, 1)
    a, b = sp.symbols("a b", positive=True)
    mass_scaled = lp*epsilon**(-a)
    radius_scaled = mass_scaled*epsilon**b
    check("two-scale curvature classification", 48*mass_scaled**2*lp**4/radius_scaled**6, 48*epsilon**(4*a-6*b))
    regulator_a = sp.symbols("regulator_a", real=True)
    new_regulator = epsilon/(1+regulator_a*epsilon)
    check("regulator finite-part reparametrization", 1/epsilon, 1/new_regulator-regulator_a)
    z, xi, u, q = sp.symbols("z xi u q", positive=True)
    check("Borel pole residue", sp.residue(sp.exp(-xi/z)/(1-xi),xi,1), -sp.exp(-1/z))
    check("weak-tide integrability primitive q!=1", sp.diff(u**(1-q)/(1-q),u), u**(-q))
    check("weak-tide logarithmic boundary primitive", sp.diff(sp.log(u),u), 1/u)

    # Check the proposed double-null convention directly from its connection.
    uu, vv = sp.symbols("u_coord v_coord", real=True)
    radius = sp.Function("radius")(uu,vv)
    omega = sp.Function("Omega")(uu,vv)
    null_coordinates = (uu,vv,theta,phi)
    null_metric = sp.Matrix([[0,-omega**2/2,0,0],[-omega**2/2,0,0,0],
                            [0,0,radius**2,0],[0,0,0,radius**2*sp.sin(theta)**2]])
    null_gamma = connection(null_metric,null_coordinates)
    null_riemann = curvature(null_gamma,null_coordinates)
    ric_uu = sum(null_riemann(a,0,a,0) for a in range(4))
    target_uu = -2/radius*(sp.diff(radius,uu,2)-2*sp.diff(omega,uu)*sp.diff(radius,uu)/omega)
    check("double-null R_uu normalization", ric_uu,target_uu)
    inv_null = null_metric.inv()
    dr = sp.Matrix([sp.diff(radius,c) for c in null_coordinates])
    check("double-null areal-radius gradient norm", (dr.T*inv_null*dr)[0],
          -4*sp.diff(radius,uu)*sp.diff(radius,vv)/omega**2)
    print(f"\nSUCCESS: {len(CHECKS)}/{len(CHECKS)} exact symbolic checks passed.")
    print("General mathematical proofs, asymptotic realization, and physical claims were not machine-verified.")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, ValueError, TypeError) as exc:
        print(f"VERIFICATION FAILED: {exc}", file=sys.stderr)
        sys.exit(1)
