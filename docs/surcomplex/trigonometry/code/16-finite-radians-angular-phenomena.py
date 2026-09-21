#!/usr/bin/env python3
"""Exact finite algebra and Taylor checks for Surcomplex Trigonometry.

Requires SymPy. This is not a surreal-number implementation or a formal
verification of the general theorems. Run: python verify_examples.py
The report is written next to this script unless --output is supplied.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import platform
import sys
import sympy as sp


checks: list[str] = []


def zero(name: str, expression: sp.Expr) -> None:
    """Require a symbolic expression to vanish identically."""
    value = sp.cancel(sp.expand(expression))
    if value != 0:
        value = sp.simplify(value)
    if value != 0:
        raise AssertionError(f"{name}: nonzero remainder {value}")
    checks.append(name)


def truth(name: str, condition: bool) -> None:
    if not condition:
        raise AssertionError(name)
    checks.append(name)


def series(name: str, expression: sp.Expr, variable: sp.Symbol,
           expected: sp.Expr, order: int) -> None:
    zero(f"{name} (mod {variable}^{order})",
         sp.series(expression - expected, variable, 0, order).removeO())


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("verification_report.txt"))
    args = parser.parse_args()
    x, y, p, q, t, u, z = sp.symbols("x y p q t u z")
    I, R = sp.I, sp.Rational
    cayley_cos = lambda v: (1-v*v)/(1+v*v)
    cayley_sin = lambda v: 2*v/(1+v*v)
    c, s = cayley_cos, cayley_sin

    # Finite Euclidean and rational-angle algebra.
    zero("Lagrange dot/determinant identity",
         (x*p+y*q)**2+(x*q-y*p)**2-(x*x+y*y)*(p*p+q*q))
    zero("Cayley norm", c(t)**2+s(t)**2-1)
    add = (t+u)/(1-t*u)
    zero("Cayley cosine addition", c(add)-c(t)*c(u)+s(t)*s(u))
    zero("Cayley sine addition", s(add)-s(t)*c(u)-c(t)*s(u))
    zero("Homogeneous angle addition norm",
         (p*u+q*t)**2+(q*u-p*t)**2-(p*p+q*q)*(t*t+u*u))
    zero("Directed inscribed-angle identity",
         ((u-z)/(t-z))/((1/u-1/z)/(1/t-1/z))-u/t)

    a, b, cside, d = sp.symbols("a b c d", positive=True)
    semiper = (a+b+cside)/2
    xx = (b*b+cside*cside-a*a)/(2*cside)
    yy2 = b*b-xx*xx
    heron = semiper*(semiper-a)*(semiper-b)*(semiper-cside)
    zero("Heron factorization", cside*cside*yy2/4-heron)
    cosA = (b*b+cside*cside-a*a)/(2*b*cside)
    zero("Positive half-angle sine squared",
         (1-cosA)/2-(semiper-b)*(semiper-cside)/(b*cside))
    zero("Positive half-angle cosine squared",
         (1+cosA)/2-semiper*(semiper-a)/(b*cside))
    zero("Half-angle inradius squared",
         (semiper-b)*(semiper-cside)/(semiper*(semiper-a))
         -heron/(semiper**2*(semiper-a)**2))
    zero("Circumcenter norm",
         cside*cside/4+(b*b-cside*xx)**2/(4*yy2)
         -a*a*b*b/(4*yy2))
    flatq = d*(2*(b+cside)-d)/(4*b*cside)
    zero("Triangle defect and half-angle identity",
         flatq-(1+cosA.subs(a,b+cside-d))/2)

    sa, sb, ca, cb = s(t), s(u), c(t), c(u)
    sc = sa*cb+ca*sb
    spreads = (sa*sa, sb*sb, sc*sc)
    zero("Triple-spread relation",
         sum(spreads)**2-2*sum(v*v for v in spreads)-4*sp.prod(spreads))
    # Ptolemy addition identity via three rational half-angle parameters.
    sg, cg = s(z), c(z)
    sin_ab = sa*cb+ca*sb
    cos_ab = ca*cb-sa*sb
    sin_bg = sb*cg+cb*sg
    sin_abg = sin_ab*cg+cos_ab*sg
    zero("Ptolemy sine addition identity",
         sin_ab*sin_bg-sa*sg-sb*sin_abg)
    sin_diff, sin_sum = sa*cb-ca*sb, sa*cb+ca*sb
    cos_diff, cos_sum = ca*cb+sa*sb, ca*cb-sa*sb
    # Here A=2*atan(t), B=2*atan(u); tangent half-sum/difference are rational.
    zero("Tangent law in two angle parameters",
         (sa-sb)/(sa+sb)-((t-u)/(1+t*u))/((t+u)/(1-t*u)))

    # Displayed small-angle and collision expansions.
    series("Sine", sp.sin(t), t, t-t**3/6+t**5/120, 7)
    series("Cosine defect", 1-sp.cos(t), t,
           t*t/2-t**4/24+t**6/720, 8)
    series("Tangent", sp.tan(t), t, t+t**3/3+2*t**5/15, 7)
    series("Arctangent", sp.atan(t), t, t-t**3/3+t**5/5, 7)
    series("Arcsine", sp.asin(t), t, t+t**3/6+3*t**5/40, 7)
    series("Chord/angle ratio", 2*sp.sin(t/2)/t, t,
           1-t*t/24+t**4/1920, 6)
    series("Flattening expansion with q=t^2", sp.asin(t)/t, t,
           1+t*t/6+3*t**4/40+5*t**6/112, 8)
    # d=2*t^2 changes the extremum inverse to 2*asin(t).
    series("Cosine-fold expansion with d=2*t^2", sp.asin(t)/t, t,
           1+(2*t*t)/12+3*(2*t*t)**2/160+5*(2*t*t)**3/896, 8)
    zero("Cosine-fold exact inverse",
         sp.cos(2*sp.asin(t))-(1-2*t*t))

    # Sharpness coefficients: 0<tau<1 is the intended real-germ range.
    tau = sp.symbols("tau", positive=True)
    root = sp.asin(sp.sqrt(tau*tau-d))
    first = sp.diff(root,d).subs(d,0)
    second = sp.diff(root,d,2).subs(d,0)/2
    zero("Conditioned root first coefficient",
         first+1/(2*tau*sp.sqrt(1-tau*tau)))
    zero("Conditioned root second coefficient",
         second-(2*tau*tau-1)/(8*tau**3*(1-tau*tau)**R(3,2)))

    # Positivity windows, exact degree, and a positive spectral factor.
    e = sp.symbols("e", positive=True)
    bad = (x-e)**2-e**4
    zero("Hidden negative value at sin(theta)=epsilon", bad.subs(x,e)+e**4)
    zero("Hidden window lower boundary", bad.subs(x,e-e*e))
    zero("Hidden window upper boundary", bad.subs(x,e+e*e))
    zero("Ordinary zero-angle value", bad.subs(x,0)-(e*e-e**4))
    lor = (u-1/u)/(2*I)
    bad_laurent = sp.expand((lor-e)**2-e**4)
    truth("Hidden-window example has Laurent degree exactly two",
          sp.Poly(sp.expand(u*u*bad_laurent),u).degree()==4)
    zero("Positive factor |u-(1+epsilon)|^2",
         (u-1-e)*(1/u-1-e)-(e*e+2*(1+e)*(1-(u+1/u)/2)))

    # Coupled angular system in sine coordinates.
    X,Y,S,U = sp.symbols("X Y S U")
    zero("Coupled diagonal sum", ((X+Y)/2)**2+((X-Y)/2)**2-(X*X+Y*Y)/2)
    zero("Coupled diagonal product", ((X+Y)/2)*((X-Y)/2)-(X*X-Y*Y)/4)
    gb = sp.groebner([X*X-S-2*U,Y*Y-S+2*U],X,Y)
    truth("Coupled quotient basis 1,X,Y,XY (leading monomials X^2,Y^2)",
          {tuple(poly.LM().exponents) for poly in gb.polys}=={(2,0),(0,2)})
    zero("Coupled sine-coordinate Jacobian",
         sp.det(sp.Matrix([[2*x,2*y],[y,x]]))-2*(x*x-y*y))
    zero("Coupled collision discriminant", (S+2*U)*(S-2*U)-(S*S-4*U*U))

    # Exact quadrature: cyclotomic arithmetic, not rounded complex roots.
    zz = sp.symbols("zeta")
    cyclo = sp.Poly(sp.cyclotomic_poly(5,zz),zz,domain=sp.QQ)
    for k in range(-4,5):
        sm = sum(zz**((j*k)%5) for j in range(5))
        rem = sp.rem(sp.Poly(sm,zz),cyclo).as_expr()
        zero(f"Five-point Fourier orthogonality, frequency {k}",
             rem-(5 if k==0 else 0))
    # Orthogonality covers all differences of frequencies of degree <=2.
    coeff = sp.symbols("c_m2 c_m1 c_0 c_p1 c_p2")
    T = dict(zip(range(-2,3),coeff))
    for k in range(-2,3):
        recovered = 0
        for ell in range(-2,3):
            sm = sum(zz**((j*(ell-k))%5) for j in range(5))
            rem = sp.rem(sp.Poly(sm,zz),cyclo).as_expr()
            recovered += T[ell]*rem/5
        zero(f"Five-point coefficient reconstruction, k={k}",recovered-T[k])

    cc,ss = (u+1/u)/2,(u-1/u)/(2*I)
    for n in range(1,7):
        zero(f"Chebyshev cosine identity, n={n}",
             sp.chebyshevt(n,cc)-(u**n+u**(-n))/2)
        zero(f"Chebyshev sine identity, n={n}",
             ss*sp.chebyshevu(n-1,cc)-(u**n-u**(-n))/(2*I))

    # Complex sine/cosine and quadratic inverse in the exponential coordinate.
    Sin,Cos = (u-1/u)/(2*I),(u+1/u)/2
    zero("Complex sine/cosine identity",Sin*Sin+Cos*Cos-1)
    w = sp.symbols("w")
    zero("Sine inversion quadratic",2*I*u*(Sin-w)-(u*u-2*I*w*u-1))
    rootq = I*w+sp.sqrt(1-w*w)
    zero("Sine inversion quadratic root",rootq*rootq-2*I*w*rootq-1)
    zero("Second sine phase is minus reciprocal",
         (I*w+sp.sqrt(1-w*w))*(I*w-sp.sqrt(1-w*w))+1)

    report = [
        "SURCOMPLEX TRIGONOMETRY — EXACT SYMBOLIC CHECKS",
        f"Python: {platform.python_version()}", f"SymPy: {sp.__version__}",
        f"Result: PASS ({len(checks)} checks)", "",
        *[f"{i:02d}. PASS  {name}" for i,name in enumerate(checks,1)], "",
        "Scope: finite polynomial/rational identities and finite formal-series coefficients.",
        "Not a representation of arbitrary surreal numbers; not proof-assistant verification.",
        "General theorems and support arguments are proved in the accompanying article.",
    ]
    text = "\n".join(report)+"\n"
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(text,encoding="utf-8")
    print(text,end="")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (AssertionError,OSError) as exc:
        print(f"VERIFICATION FAILED: {exc}",file=sys.stderr)
        sys.exit(1)
