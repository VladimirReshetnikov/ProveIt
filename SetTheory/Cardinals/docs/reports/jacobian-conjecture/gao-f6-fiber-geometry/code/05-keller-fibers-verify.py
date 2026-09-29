#!/usr/bin/env python3
"""Exact certificates for the accompanying F_6 fiber-classification article.

Requires Python 3.10+ and SymPy. No floating point arithmetic or network access.
Run: python verify.py > verification.txt
This is a computer-algebra check, not a Lean/Rocq kernel certificate.
"""
from __future__ import annotations
import platform
from pathlib import Path
import sympy as sp

T, s, r, g, u, v, w = sp.symbols("T s r g u v w")
a, b, c, rho = sp.symbols("a b c rho")
x, y, z1, z2, z3 = sp.symbols("x y z1 z2 z3")
C, p1, p2, p3, p4, eta = sp.symbols("C p1 p2 p3 p4 eta")
Q = sp.Rational


def zero(expr: sp.Expr, label: str) -> None:
    if sp.expand(expr) != 0:
        raise AssertionError(f"Identity failed: {label}")


def passed(label: str) -> None:
    print("PASS:", label, flush=True)


def mul_trunc(f: list[sp.Expr], h: list[sp.Expr]) -> list[sp.Expr]:
    if len(f) != len(h):
        raise ValueError("Truncation lengths must agree")
    return [sp.expand(sum(f[j] * h[i-j] for j in range(i+1)))
            for i in range(len(f))]


def pow_trunc(f: list[sp.Expr], n: int) -> list[sp.Expr]:
    out = [sp.Integer(1)] + [sp.Integer(0)] * (len(f)-1)
    for _ in range(n):
        out = mul_trunc(out, f)
    return out


def substitute_trunc(poly: sp.Poly, series: list[list[sp.Expr]]) -> list[sp.Expr]:
    n = len(series[0])
    powers = [{j: pow_trunc(ser, j) for j in range(poly.degree(i)+1)}
              for i, ser in enumerate(series)]
    out = [sp.Integer(0)] * n
    for exps, coeff in poly.terms():
        term = [coeff] + [sp.Integer(0)] * (n-1)
        for j, e in enumerate(exps):
            term = mul_trunc(term, powers[j][e])
        out = [sp.expand(out[j] + term[j]) for j in range(n)]
    return out


def simple_root_factor(poly: sp.Poly) -> sp.Poly:
    """Monic product of the roots whose multiplicity is exactly one."""
    f = poly.monic()
    d = f.gcd(f.diff())
    h = f.exquo(d)
    return h.exquo(h.gcd(d)).monic()


def complex_fiber_size(target: tuple) -> int:
    """Count geometric points, not rational points, for an exact rational target."""
    if len(target) != 5:
        raise ValueError("Expected (C,p1,p2,p3,p4)")
    cc, pp1, pp2, pp3, pp4 = map(sp.Rational, target)
    if cc == 0:
        return 1 if pp1**2 + 4*pp2 == 0 else 3
    yy1, yy2, yy3, yy4 = (cc*pp1, cc**2*pp2, cc**3*pp3, cc**4*pp4)
    aa = yy1+1
    bb = yy4+yy2**2-yy1*yy3-2*yy2+yy1
    ccc = yy3-yy2
    f = sp.Poly(2*T**6-2*T**5-T**3+aa*T**2+bb*T+ccc, T, domain=sp.QQ)
    return simple_root_factor(f).degree()


def mod_power(base: sp.Poly, exponent: int, modulus: sp.Poly) -> sp.Poly:
    """Repeated squaring in a finite polynomial quotient ring."""
    result = sp.Poly(1, T, modulus=modulus.get_modulus())
    base = base.rem(modulus)
    while exponent:
        if exponent & 1:
            result = (result*base).rem(modulus)
        base = (base*base).rem(modulus)
        exponent >>= 1
    return result


def check_irreducible(expr: sp.Expr, prime: int) -> None:
    f = sp.Poly(expr, T, modulus=prime).monic()
    n = f.degree()
    tt = sp.Poly(T, T, modulus=prime)
    for ell in sp.factorint(n):
        residue = mod_power(tt, prime**(n//ell), f)-tt
        divisor = f.gcd(residue)
        assert divisor.degree() == 0
        print(f"  F_{prime}, degree {n}: gcd(T^(p^{n//ell})-T,f) = 1")
    assert (mod_power(tt, prime**n, f)-tt).is_zero
    print(f"  F_{prime}, degree {n}: T^(p^{n})-T = 0 modulo f")


def main() -> None:
    print("Exact F_6 verification")
    print("Python", platform.python_version(), "SymPy", sp.__version__)
    print("All coefficients are exact rational numbers or finite-field elements.\n")

    A = s+T*r+T**2-T**3
    B = r-A**2+2*T**4-2*T**5
    X1 = 2*r*T-r+2*s-10*T**5+8*T**4-2*T**3+5*T**2-2*T
    zero(X1+sp.Matrix([A, 2*T*A+s, B]).jacobian([T,s,r]).det(), "X1 determinant")
    delta = sp.Matrix([1,T,T**2,s])
    XX = sp.Matrix([X1,A+T*X1,2*T*A+s+T**2*X1,B+s*X1])
    sweep = XX+g*delta
    zero(sweep.jacobian([g,T,s,r]).det()-g, "sweep determinant")
    passed("sweep Jacobian = gamma")

    xi = sp.symbols("xi1:5")
    xi1, xi2, xi3, xi4 = xi
    stage = [1-29*xi1+999*xi1**2+355*xi1*xi2-41553*xi1**3+xi4,
             1+27*xi1-5*xi2, xi1-12*xi2+Q(2128,5)*xi1**2+xi3,
             -4*xi1-10*xi2]
    inv1 = (2*(u-1)-w)/58
    inv2 = -(4*(u-1)+27*w)/290
    inv3 = v-inv1+12*inv2-Q(2128,5)*inv1**2
    inv4 = g-1+29*inv1-999*inv1**2-355*inv1*inv2+41553*inv1**3
    inverse = [inv1,inv2,inv3,inv4]
    for i, st in enumerate(stage):
        zero(st.subs(dict(zip(xi,inverse)), simultaneous=True)-[g,u,v,w][i], "stage inverse")
    for i, iv in enumerate(inverse):
        zero(iv.subs(dict(zip([g,u,v,w],stage)), simultaneous=True)-xi[i], "inverse stage")
    zero(sp.Matrix(stage).jacobian(xi).det()+290, "stage determinant")
    passed("stage is an explicitly inverted polynomial automorphism, determinant -290")

    E = []
    for i, si in enumerate(sweep):
        ee = sp.cancel(si.subs({T:g*u,s:g**3*v,r:g**4*w})/g**(i+1))
        E.append(sp.Poly(ee,g,u,v,w,domain=sp.QQ))
    at_zero = [1-2*u,u-u**2,u**2+v,u**4+(1-2*u)*v+w]
    for i in range(4):
        zero(E[i].as_expr().subs(g,0)-at_zero[i], "gamma zero values")
    passed("gamma divisibility and all four values E_i(0,u,v,w)")

    series = [[1,-29*y,999*y*y,355*y*z1-41553*y**3,z3],
              [1,27*y,-5*z1,0,0],
              [0,y,-12*z1+Q(2128,5)*y*y,z2,0],
              [0,-4*y,-10*z1,0,0]]
    jets = [y,29*z1-Q(4636,5)*y*y,
            5*z2-1041*y*z1+Q(6039,5)*y**3,
            -2*z3+5*y*z2-1041*z1*z1-Q(463585,25)*y*y*z1+Q(74000249,25)*y**4]
    for i, ee in enumerate(E):
        coefficients = substitute_trunc(ee,series)
        for j in range(i+1):
            zero(coefficients[j], "x divisibility")
        zero(coefficients[i+1]-jets[i], "hyperplane jet")
        print(f"  J_{i+1} = {jets[i]}")
    zero(sp.Matrix(jets).jacobian([y,z1,z2,z3]).det()+290, "boundary Jacobian")
    passed("all x-divisibilities, boundary jets, and boundary determinant")

    Y1,Y2,Y3,Y4 = sp.symbols("Y1 Y2 Y3 Y4")
    sr = {s:Y3-2*T*Y2+T*T*Y1,
          r:Y4+Y2*Y2-Y1*Y3+2*T**5-2*T**4}
    RY = 2*T**6-2*T**5-T**3+(Y1+1)*T*T+(Y4+Y2*Y2-Y1*Y3-2*Y2+Y1)*T+Y3-Y2
    zero(A.subs(sr)-(Y2-T*Y1)-RY, "elimination R")
    zero(Y1-X1.subs(sr)-sp.diff(RY,T)+2*RY, "gamma identity")
    gamma_root = sp.diff(RY,T)
    recon_sweep = sweep.subs(sr).subs(g,gamma_root)
    for i, yy in enumerate([Y1,Y2,Y3,Y4]):
        zero(sp.rem(sp.expand(recon_sweep[i]-yy), RY,T), "sweep reconstruction mod R")
    passed("exact sextic elimination, gamma = R' - 2R, and reconstruction modulo R")

    R = 2*T**6-2*T**5-T**3+a*T*T+b*T+c
    qc = T**3-T*T/2-T/8-Q(5,16)
    star = {a:Q(21,32),b:Q(5,32),c:Q(25,128)}
    zero(R.subs(star)-2*qc**2, "unique square")
    assert sp.discriminant(qc,T) == -Q(401,128)
    for m in [1,2,3]:
        assert 1369*m*(6-m) != 125*(3-m)**2
    passed("triple-double square and the integer obstructions to two-root patterns")

    witnesses = [(6,{a:0,b:1,c:1}), (4,{a:1,b:0,c:0}),
                 (3,{a:0,b:0,c:0}), (2,{a:-Q(3,8),b:-Q(1,8),c:-Q(1,16)}),
                 (0,star)]
    for size, params in witnesses:
        f = sp.Poly(R.subs(params),T,domain=sp.QQ)
        assert simple_root_factor(f).degree() == size
        print(f"  {size} simple roots: {sp.factor(f.as_expr())}")
    tri = {a:-30*rho**4+20*rho**3+3*rho,
           b:48*rho**5-30*rho**4-3*rho**2,
           c:-20*rho**6+12*rho**5+rho**3}
    cofactor, rem = sp.div(R.subs(tri),(T-rho)**3,T)
    zero(rem,"triple-root division")
    K = 4320*rho**6-4320*rho**5+540*rho**4-448*rho**3+384*rho**2+36*rho+35
    H4 = 40*rho**3-20*rho**2-1
    zero(sp.discriminant(cofactor,T)+4*K,"cofactor discriminant")
    assert sp.degree(K,rho)==6 and sp.gcd(K,H4)==1
    assert sp.gcd(H4,rho*(3*rho-1))==1
    print("  Triple cofactor =",cofactor)
    print("  K(rho) =", K)
    passed("nonempty (3,2,1) and (4,1,1) strata certificates")

    ys = [C*p1,C*C*p2,C**3*p3,C**4*p4]
    abc = [ys[0]+1,ys[3]+ys[1]**2-ys[0]*ys[2]-2*ys[1]+ys[0],ys[2]-ys[1]]
    missing = {p1:-Q(11,32)/C,p2:eta/C**2,p3:(eta+Q(25,128))/C**3,
               p4:(-eta*eta+Q(53,32)*eta+Q(1773,4096))/C**4}
    for f, value in zip(abc,star.values()):
        zero(sp.cancel(f.subs(missing)-value), "omitted surface")
    assert complex_fiber_size((1,-Q(11,32),0,Q(25,128),Q(1773,4096))) == 0
    assert complex_fiber_size((0,0,0,0,0)) == 1
    assert complex_fiber_size((0,0,1,0,0)) == 3
    assert complex_fiber_size((1,-1,0,1,1)) == 6
    passed("omitted-surface parametrization and exact sample fiber counts")

    D = sp.discriminant(R,T)
    double_b = -12*rho**5+10*rho**4+3*rho**2-2*a*rho
    double_c = 10*rho**6-8*rho**5-2*rho**3+a*rho**2
    zero(R.subs({T:rho,b:double_b,c:double_c},simultaneous=True), "double-root incidence")
    zero(sp.diff(R,T).subs({T:rho,b:double_b,c:double_c},simultaneous=True), "double-root derivative")
    assert sp.diff(D,c).subs({a:1,b:0,c:0}) == 432
    # Check C-adic coefficients only through C^2; omitted higher terms cannot contribute.
    dseries = substitute_trunc(sp.Poly(D,a,b,c), [[1,p1,0],[0,p1,-2*p2],[0,0,-p2]])
    zero(dseries[0],"C^0 discriminant")
    zero(dseries[1],"C^1 discriminant")
    zero(dseries[2]+108*(p1*p1+4*p2),"C^2 discriminant")
    passed("discriminant incidence, reducedness witness, and D = C^2[-108 H + O(C)]")
    Path(__file__).with_name("sextic_discriminant.txt").write_text(str(sp.expand(D))+"\n",encoding="utf-8")

    quartic = T**4+u*T*T+v*T+w
    quartic_disc = 256*w**3-128*u*u*w*w+144*u*v*v*w-27*v**4+16*u**4*w-4*u**3*v*v
    zero(sp.discriminant(quartic,T)-quartic_disc,"quartic local normal form")
    passed("universal quartic discriminant in the local analytic type table")

    P = 2*T**6-2*T**5-T**3+T
    critical = -4*c*(32*c+11)*(11664*c**3-6976*c*c+5485*c-1372)
    zero(sp.discriminant(P+c,T)-critical,"Morse discriminant")
    assert sp.Poly(critical,c,domain=sp.QQ).gcd(sp.Poly(sp.diff(critical,c),c,domain=sp.QQ)).degree() == 0
    zero(sp.diff(P,T)-(T-1)*(2*T-1)*(6*T**3+4*T*T+3*T+1),"critical points")
    passed("five distinct simple critical values for the S_6 monodromy line")

    example = P+1
    assert sp.discriminant(example,T) == -1513772 == -4*13*43*677
    f7 = T**6-T**5+3*T**3-3*T-3
    f11 = T**5-4*T**4+T**3+2*T*T+5*T+2
    f269 = T*T+71*T+134
    for prime, product in [(7,2*f7),(11,2*(T+3)*f11),
                          (269,2*(T+76)*(T+98)*(T-132)*(T-114)*f269)]:
        assert sp.isprime(prime) and 1513772 % prime != 0
        assert sp.Poly(example-product,T,modulus=prime).is_zero
    check_irreducible(f7,7)
    check_irreducible(f11,11)
    check_irreducible(f269,269)
    passed("exact Frobenius cycle certificates (6), (5,1), and (2,1,1,1,1)")

    print("\nALL CHECKS PASSED")
    print("The general classification, normal-crossing, properness, and group arguments")
    print("are mathematical proofs in the article, not assertions proved by this script.")


if __name__ == "__main__":
    main()
