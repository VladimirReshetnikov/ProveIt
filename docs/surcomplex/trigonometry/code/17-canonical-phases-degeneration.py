#!/usr/bin/env python3
"""Exact symbolic consistency checks for Surcomplex Trigonometry.

These checks verify algebraic identities and finite Taylor jets. They do not
construct the proper class No, establish Hahn summability, or formally verify
the article's general theorems. Run with Python 3.9+ and SymPy.
"""
from pathlib import Path
import sys
import sympy as sp

RESULTS = []


def check(name: str, expression) -> None:
    """Check that an exact expression vanishes; fail on the first discrepancy."""
    residual = sp.factor(sp.cancel(sp.expand(expression)))
    if residual != 0:
        raise AssertionError(f"{name}: nonzero residual: {residual}")
    RESULTS.append(f"PASS  {name}")


def jet(expression, variable, order: int):
    return sp.series(expression, variable, 0, order).removeO().expand()


def run() -> None:
    x, y, u, v = sp.symbols("x y u v", real=True)
    check("Euclidean Gram identity in two dimensions",
          (x*u+y*v)**2+(x*v-y*u)**2-(x*x+y*y)*(u*u+v*v))

    t = sp.symbols("t", real=True)
    X, Y = (1-t*t)/(1+t*t), 2*t/(1+t*t)
    check("Stereographic map lands on the unit circle", X*X+Y*Y-1)
    check("Stereographic inverse y/(1+x)", Y/(1+X)-t)
    check("Cayley rational expression",
          (1+sp.I*t)/(1-sp.I*t)-(X+sp.I*Y))

    a, b, c = sp.symbols("a b c", positive=True)
    s = (a+b+c)/2
    coord_x = (b*b+c*c-a*a)/(2*c)
    H2 = b*b-coord_x**2
    heron = s*(s-a)*(s-b)*(s-c)
    check("Heron factorization from the coordinate altitude", c*c*H2/4-heron)
    cos_A = (b*b+c*c-a*a)/(2*b*c)
    check("Sine half-angle square", (1-cos_A)/2-(s-b)*(s-c)/(b*c))
    check("Cosine half-angle square", (1+cos_A)/2-s*(s-a)/(b*c))
    check("Inradius/half-angle squared relation",
          heron/s**2/(s-a)**2-(s-b)*(s-c)/(s*(s-a)))
    check("Circumradius coordinate calculation",
          c*c*(1-cos_A*cos_A)+(b-c*cos_A)**2-a*a)
    phase = sp.symbols("phase", nonzero=True)
    a2 = b*b+c*c-b*c*(phase+1/phase)
    check("Triangle phase product has numerator -a^2",
          phase*(c-b/phase)*(b-c/phase)+a2)

    z1, z2, z3, z4 = sp.symbols("z1 z2 z3 z4")
    check("Ptolemy complex polynomial identity",
          (z1-z3)*(z2-z4)-(z1-z2)*(z3-z4)-(z1-z4)*(z2-z3))

    p, q = sp.symbols("p q", real=True)
    order = 9
    sn = lambda r: jet(sp.sin(r*t), t, order)
    cs = lambda r: jet(sp.cos(r*t), t, order)
    check("Sine addition jet through degree 8 in a common infinitesimal",
          jet(sn(p+q)-sn(p)*cs(q)-cs(p)*sn(q), t, order))
    check("Cosine addition jet through degree 8 in a common infinitesimal",
          jet(cs(p+q)-cs(p)*cs(q)+sn(p)*sn(q), t, order))

    ch = (a*a-b*b-c*c)/(2*b*c)
    gap = b+c-a
    check("Exact nearly-flat gap identity",
          2*b*c*(1-ch)-gap*(2*(b+c)-gap))
    length, half_sine_sq = sp.symbols("length half_sine_sq")
    numerator = (a+b)**2-length**2
    check("Triangle-inequality defect factorization",
          numerator-(a+b-length)*(a+b+length))
    check("Defect numerator after the cosine law",
          numerator.subs(length**2, (a+b)**2-4*a*b*half_sine_sq)
          -4*a*b*half_sine_sq)

    tau = sp.symbols("tau")
    Hnorm = 1-tau/8-tau**2/128-tau**3/1024
    Rnorm = 1+tau/8+3*tau**2/128+5*tau**3/1024
    check("Isosceles altitude binomial coefficients through tau^3",
          jet(sp.sqrt(1-tau/4), tau, 4)-Hnorm)
    check("Isosceles radius binomial coefficients through tau^3",
          jet((1-tau/4)**sp.Rational(-1,2), tau, 4)-Rnorm)
    h = 2*t*(1+t*t/24+3*t**4/640+5*t**6/7168)
    check("Isosceles angle jet: cos(h/2)=1-t^2/2 through degree 9",
          jet(sp.cos(h/2)-(1-t*t/2), t, 10))
    zr = sp.sqrt(2)*t*(1+t*t/12+3*t**4/160+5*t**6/896)
    check("Ramified cosine root jet through degree 9 (eta=t^2)",
          jet(sp.cos(zr)-(1-t*t), t, 10))

    A, B, C, rootD = sp.symbols("A B C rootD", real=True)
    R2 = A*A+B*B
    D = R2-C*C
    for sign in (1, -1):
        xx = (C*A-sign*rootD*B)/R2
        yy = (C*B+sign*rootD*A)/R2
        label = "+" if sign == 1 else "-"
        check(f"Line-circle {label} solution lies on the line", A*xx+B*yy-C)
        circ = sp.factor(xx*xx+yy*yy-1)
        check(f"Line-circle {label} solution lies on the circle",
              sp.expand(sp.together(circ).as_numer_denom()[0]).subs(rootD**2, D))
        check(f"Angular derivative at line-circle {label} solution",
              B*xx-A*yy+sign*rootD)

    W, d, rr = sp.symbols("W d rr")
    basis = (sp.Integer(1), W)
    residue = lambda f: sp.rem(sp.expand(f), W*W-d, W).coeff(W, 1)
    gram = sp.Matrix([[residue(i*j) for j in basis] for i in basis])
    check("Collision pairing determinant is -1", gram.det()+1)
    check("Collision pairing diagonal entry (1,1)", gram[0,0])
    check("Collision pairing off-diagonal entry is 1", gram[0,1]-1)
    check("Collision pairing diagonal entry (W,W)", gram[1,1])
    coeff = sp.symbols("g0:6")
    g = sum(coeff[k]*W**k for k in range(6))
    divided = (g.subs(W,rr)-g.subs(W,-rr))/(2*rr)
    check("Separated residue sum equals quotient functional for degree <=5",
          residue(g).subs(d,rr*rr)-divided)
    check("Double-point residue equals g'(0)",
          residue(g).subs(d,0)-sp.diff(g,W).subs(W,0))
    reduced = sp.rem(g,W*W-d,W)
    aa, bb = reduced.coeff(W,0), reduced.coeff(W,1)
    matrix = sp.Matrix([[aa,bb*d],[bb,aa]])
    check("Trace-Jacobian identity in the quadratic algebra",
          matrix.trace()-residue(2*W*g))

    cv, sv, eps = sp.symbols("cv sv eps", nonzero=True)
    U = sp.symbols("U")
    inverse_q = -U-cv*U**2/2-(3*cv**2+sv**2)*U**3/6
    normalized_F = -q-cv*q*q/2+sv*sv*q**3/6
    check("Normalized inverse-cosine series through cubic order",
          jet(normalized_F.subs(q,inverse_q)-U, U, 4))
    shift2 = -eps/sv-cv*eps**2/(2*sv**3)
    check("Second-order inverse-cosine equation",
          jet(cv*sp.cos(shift2)-sv*sp.sin(shift2)-cv-eps, eps, 3))
    third_residual = jet(cv*sp.cos(shift2)-sv*sp.sin(shift2)-cv-eps, eps, 4)
    check("First omitted inverse-cosine residual coefficient",
          third_residual.coeff(eps,3)+(3*cv**2+sv**2)/(6*sv**4))

    reals = sp.symbols("x0:4", real=True)
    imags = sp.symbols("y0:4", real=True)
    data = [reals[j]+sp.I*imags[j] for j in range(4)]
    ft = [sp.expand(sum(data[j]*sp.I**(-j*k) for j in range(4))/4)
          for k in range(4)]
    for j in range(4):
        check(f"Exact four-point Fourier inversion at sample {j}",
              sum(ft[k]*sp.I**(j*k) for k in range(4))-data[j])
    sqnorm = lambda z: sp.expand(z*sp.conjugate(z))
    check("Exact four-point Parseval with eight real symbolic coordinates",
          sum(map(sqnorm,data))-4*sum(map(sqnorm,ft)))

    aa, bb, cc = sp.symbols("aa bb cc")
    G = sp.Matrix([[1,cc,bb],[cc,1,aa],[bb,aa,1]])
    check("Spherical tangent Gram identity",
          (1-bb*bb)*(1-cc*cc)-(aa-bb*cc)**2-G.det())
    check("Hyperbolic tangent Gram identity",
          (bb*bb-1)*(cc*cc-1)-(bb*cc-aa)**2-G.det())


def main() -> int:
    report = Path(__file__).resolve().with_name("verification_report.txt")
    header = ["SURCOMPLEX TRIGONOMETRY — EXACT SYMBOLIC CHECKS",
              f"Python: {sys.version.split()[0]}", f"SymPy: {sp.__version__}", "",
              "Scope: finite polynomial identities and explicitly stated Taylor jets.",
              "Not a proof-assistant verification; not a construction of No.", ""]
    try:
        run()
    except Exception as exc:
        text = "\n".join(header+RESULTS+["", f"FAIL: {exc}"])+"\n"
        report.write_text(text, encoding="utf-8")
        print(text)
        return 1
    text = "\n".join(header+RESULTS+["", f"RESULT: {len(RESULTS)} checks passed."])+"\n"
    report.write_text(text, encoding="utf-8")
    print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
