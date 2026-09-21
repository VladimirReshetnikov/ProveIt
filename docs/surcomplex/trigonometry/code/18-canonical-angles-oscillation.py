#!/usr/bin/env python3
"""Exact finite algebra and Taylor checks for Trigonometry on the Surcomplex Plane.

Requires Python 3.9+ and SymPy. This does NOT implement the surreal class or
formally verify the proofs, summability, transfinite lifting, or branch choices.
Run: python verify_examples.py --report verification_report.txt
"""
from __future__ import annotations

import argparse
from pathlib import Path
import platform
import sys
from typing import List

try:
    import sympy as s
except ImportError:
    raise SystemExit("SymPy is required. Install it with: python -m pip install sympy")

CHECKS: List[str] = []


def zero(name: str, expression: s.Expr) -> None:
    """Check a rational/polynomial identity using exact symbolic arithmetic."""
    result = s.cancel(s.expand(expression))
    if result != 0:
        result = s.simplify(result)
    if result != 0:
        raise AssertionError(f"{name}: nonzero residual {result}")
    CHECKS.append(name)


def series_equal(name: str, expression: s.Expr, expected: s.Expr,
                 variable: s.Symbol, order: int) -> None:
    zero(name, s.series(expression, variable, 0, order).removeO() - expected)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", type=Path, help="Optional UTF-8 report path.")
    args = parser.parse_args()
    x, y, u, v, t, h, e = s.symbols("x y u v t h e", real=True)
    I = s.I
    R = s.Rational

    # Ordered-field geometry: algebraic parts independent of an Archimedean axiom.
    zero("Gram/dot-determinant identity",
         (x*u+y*v)**2+(x*v-y*u)**2-(x*x+y*y)*(u*u+v*v))
    ct, st = (1-t*t)/(1+t*t), 2*t/(1+t*t)
    zero("Cayley circle coordinates have norm one", ct**2+st**2-1)
    zero("Cayley inverse half-angle coordinate", st/(1+ct)-t)
    U = (1+I*t)/(1-I*t)
    zero("Cayley complex and real coordinate formulas", U-ct-I*st)
    V = (1+I*u)/(1-I*u)
    tangent_sum = (t+u)/(1-t*u)
    zero("Cayley angle-addition law",
         U*V-(1+I*tangent_sum)/(1-I*tangent_sum))
    z1,z2,z3,z4 = s.symbols("z1 z2 z3 z4")
    zero("Four-point identity underlying Ptolemy",
         (z1-z3)*(z2-z4)-(z1-z2)*(z3-z4)-(z1-z4)*(z2-z3))
    a,b,c = s.symbols("a b c", positive=True)
    X = (b*b+c*c-a*a)/(2*c)
    hp = (a+b+c)*(-a+b+c)*(a-b+c)*(a+b-c)
    zero("Heron coordinate factorization", 4*c*c*(b*b-X*X)-hp)
    half_perimeter = (a+b+c)/2
    zero("Heron product convention",
         hp/16-half_perimeter*(half_perimeter-a)*(half_perimeter-b)*(half_perimeter-c))
    zero("Half-angle sine square from cosine law",
         (1-(b*b+c*c-a*a)/(2*b*c))/2
         -(half_perimeter-b)*(half_perimeter-c)/(b*c))
    zero("Half-angle cosine square from cosine law",
         (1+(b*b+c*c-a*a)/(2*b*c))/2
         -half_perimeter*(half_perimeter-a)/(b*c))
    zero("Circumradius coordinate identity",
         c*c/4+(x*x+y*y-c*x)**2/(4*y*y)
         -((x-c)**2+y*y)*(x*x+y*y)/(4*y*y))
    weights = s.symbols("w0:3", positive=True)
    px, py = s.symbols("px0:3", real=True), s.symbols("py0:3", real=True)
    W = sum(weights)
    lhs = (sum(weights[j]*px[j] for j in range(3))**2
           +sum(weights[j]*py[j] for j in range(3))**2)
    rhs = W*sum(weights[j]*(px[j]**2+py[j]**2) for j in range(3))
    rhs -= sum(weights[j]*weights[k]*((px[j]-px[k])**2+(py[j]-py[k])**2)
               for j in range(3) for k in range(j+1,3))
    zero("Weighted vector variance identity used for Euler", lhs-rhs)
    area = s.symbols("area", positive=True)
    Rc, ri = a*b*c/(4*area), area/half_perimeter
    zero("Euler pairwise-weight and 2Rr identity",
         (a*b*c*c+a*c*b*b+b*c*a*a)/(4*half_perimeter**2)-2*Rc*ri)

    # Laurent-variable verification of multiple-angle and algebraization formulas.
    Z = s.symbols("Z", nonzero=True)
    C, S = (Z+1/Z)/2, (Z-1/Z)/(2*I)
    for n in range(9):
        zero(f"Chebyshev cosine identity n={n}", s.chebyshevt(n,C)-(Z**n+Z**(-n))/2)
    for n in range(1,9):
        zero(f"Chebyshev sine identity n={n}", S*s.chebyshevu(n-1,C)-(Z**n-Z**(-n))/(2*I))
    w = s.symbols("w")
    zero("Complex sine quadratic equation", 2*I*Z*(S-w)-(Z*Z-2*I*w*Z-1))
    coeff = s.symbols("c0:7")
    laurent = sum(coeff[k+3]*Z**k for k in range(-3,4))
    zero("Frequency-three polynomial algebraization",
         Z**3*laurent-sum(coeff[j]*Z**j for j in range(7)))

    # Formal infinitesimal series, checked before any surreal substitution.
    series_equal("Sine series through degree seven", s.sin(h),
                 h-h**3/6+h**5/120-h**7/5040,h,9)
    series_equal("Cosine series through degree eight", s.cos(h),
                 1-h*h/2+h**4/24-h**6/720+h**8/40320,h,10)
    series_equal("Tangent series through degree seven",s.tan(h),
                 h+h**3/3+2*h**5/15+17*h**7/315,h,9)
    series_equal("Inverse tangent series through degree seven",s.atan(h),
                 h-h**3/3+h**5/5-h**7/7,h,9)
    series_equal("Inverse sine series through degree seven",s.asin(h),
                 h+h**3/6+3*h**5/40+5*h**7/112,h,9)
    series_equal("Infinitesimal logarithm through degree four",s.log(1+h),
                 h-h*h/2+h**3/3-h**4/4,h,5)
    series_equal("Binomial square root through degree four",s.sqrt(1+h),
                 1+h/2-h*h/8+h**3/16-5*h**4/128,h,5)
    # delta=h^2 avoids a branch-sensitive expansion of acos at its endpoint.
    ac = 2*s.asin(h/s.sqrt(2))/(s.sqrt(2)*h)
    ac_expected = 1+h*h/12+3*h**4/160+5*h**6/896+35*h**8/18432
    series_equal("Ramified inverse-cosine coefficients through delta^4",
                 ac, ac_expected,h,10)
    for n in range(5):
        zero(f"Inverse-cosine general coefficient n={n}",
             s.expand(ac_expected).coeff(h,2*n)-s.binomial(2*n,n)/(8**n*(2*n+1)))
    d = s.symbols("d", positive=True)
    zero("Tangency derivative squared", s.diff(s.acos(1-d),d)**2-1/(d*(2-d)))
    zero("Tangency derivative magnitude squared",1-(1-d)**2-d*(2-d))

    # Thin triangle; writing the roots in unit form specifies the positive branch.
    A = (1-x)*s.sqrt(1+(h/(1-x))**2)
    B = x*s.sqrt(1+(h/x)**2)
    series_equal("Flat triangle slack through height^4", A+B-1,
                 h*h/(2*x*(1-x))-h**4*(x**(-3)+(1-x)**(-3))/8,h,6)
    series_equal("Flat circumradius unit correction through height^2",
                 A*B/(x*(1-x)), 1+h*h*(x**(-2)+(1-x)**(-2))/2,h,4)
    series_equal("Flat inradius unit correction through height^2",
                 2/(A+B+1),1-h*h/(4*x*(1-x)),h,4)
    zero("Symmetric flat circumradius exact formula",
         ((R(1,2))**2+h*h)/(2*h)-(1/(8*h)+h/2))
    series_equal("Symmetric flat inradius through height^5",
                 h/(1+s.sqrt(1+4*h*h)),h/2-h**3/2+h**5,h,7)
    series_equal("Mixed-scale triangle inradius with h=1/L",
                 (1/h+h-s.sqrt(1+h**4)/h)/2,h/2-h**3/4,h,7)

    # Finite Fourier algebra and a real-closed-field spectral factor example.
    f = s.symbols("f0:4")
    g = s.symbols("g0:4")
    F = sum(f[j]*Z**j for j in range(4))
    Gstar = sum(s.conjugate(g[j])*Z**(-j) for j in range(4))
    zero("Finite Fourier inner-product constant coefficient",
         s.expand(F*Gstar).coeff(Z,0)-sum(f[j]*s.conjugate(g[j]) for j in range(4)))
    q = (t-(1+2*I))*(t-(-3+I))
    p = s.expand(q*s.conjugate(q))
    zero("Spectral-factor example is real",p-s.conjugate(p))
    Q = s.cancel(((1+Z)/2)**2*q.subs(t,(Z-1)/(I*(Z+1))))
    if s.denom(Q) != 1:
        # Rational constants in expanded coefficients do not count as a pole.
        if s.denom(s.together(Q)).has(Z):
            raise AssertionError("Spectral factor failed polynomial cancellation")
    CHECKS.append("Spectral factor Cayley transform is a polynomial")
    QU = s.cancel(Q.subs(Z,U))
    zero("Spectral factor on the circle",QU*s.conjugate(QU)-p/(1+t*t)**2)
    qc = [s.expand(Q).coeff(Z,j) for j in range(3)]
    Qstar = sum(s.conjugate(qc[j])*Z**(-j) for j in range(3))
    spectrum = s.expand(Q*Qstar)
    zero("Spectral factor constant coefficient",
         spectrum.coeff(Z,0)-sum(qj*s.conjugate(qj) for qj in qc))
    zero("Surreal positivity counterexample Fourier decomposition",
         (C-e)**2-e**4-(R(1,2)+e**2-e**4-e*(Z+1/Z)+(Z**2+Z**(-2))/4))

    # Rational identities behind the full surreal Poincare disk.
    az, ab, zz, zb, ww, wb = s.symbols("a abar z zbar w wbar")
    phi_z = (zz-az)/(1-ab*zz)
    phi_w = (ww-az)/(1-ab*ww)
    phi_z_bar = (zb-ab)/(1-az*zb)
    phi_w_bar = (wb-ab)/(1-az*wb)
    zero("Disk automorphism norm identity",
         1-phi_z*phi_z_bar-(1-az*ab)*(1-zz*zb)/((1-ab*zz)*(1-az*zb)))
    zero("Disk automorphism difference identity",
         phi_z-phi_w-(1-az*ab)*(zz-ww)/((1-ab*zz)*(1-ab*ww)))
    zero("Disk automorphism denominator identity",
         1-phi_w_bar*phi_z
         -(1-az*ab)*(1-wb*zz)/((1-az*wb)*(1-ab*zz)))
    zero("Disk automorphism inverse",(phi_z+az)/(1+ab*phi_z)-zz)
    r, p_, co = s.symbols("r p co", real=True)
    rho2 = (r*r+p_*p_-2*r*p_*co)/(1+r*r*p_*p_-2*r*p_*co)
    zero("Hyperbolic cosine law after half-distance substitution",
         (1+rho2)/(1-rho2)
         -((1+r*r)*(1+p_*p_)-4*r*p_*co)/((1-r*r)*(1-p_*p_)))
    zero("Disk triangle-inequality extremal angle",
         rho2.subs(co,-1)-((r+p_)/(1+r*p_))**2)
    zero("Pseudohyperbolic triangle difference has nonnegative factors",
         ((r+p_)/(1+r*p_))**2-rho2
         -2*r*p_*(1+co)*(1-r*r)*(1-p_*p_)
           /((1+r*p_)**2*(1+r*r*p_*p_-2*r*p_*co)))
    zero("Hyperbolic distance addition logarithm argument",
         (1+(r+p_)/(1+r*p_))/(1-(r+p_)/(1+r*p_))
         -(1+r)*(1+p_)/((1-r)*(1-p_)))
    Xa,Xb,Xc=s.symbols("Xa Xb Xc")
    zero("Symmetric hyperbolic sine-law numerator",
         (Xb*Xb-1)*(Xc*Xc-1)-(Xb*Xc-Xa)**2
         -(1+2*Xa*Xb*Xc-Xa*Xa-Xb*Xb-Xc*Xc))

    lines = ["Exact symbolic verification report", "="*34,
             f"Python: {platform.python_version()}",f"SymPy: {s.__version__}", ""]
    lines.extend(f"PASS {j:02d}: {name}" for j,name in enumerate(CHECKS,1))
    lines.extend(["", f"RESULT: {len(CHECKS)} checks passed; no failed checks.", "",
                  "Scope: exact polynomial/rational identities and finite formal series only.",
                  "Not a model of No; not a formal proof check of summability, transfinite",
                  "lifting, class-theoretic arguments, order/branch assertions, or the article."])
    report = "\n".join(lines)+"\n"
    print(report,end="")
    if args.report is not None:
        args.report.write_text(report,encoding="utf-8")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (AssertionError, OSError) as exc:
        print(f"VERIFICATION FAILED: {exc}", file=sys.stderr)
        sys.exit(1)
