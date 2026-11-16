#!/usr/bin/env python3
"""Exact verification companion for the Bring-radical/quintic iPRA packet.

The script deliberately checks only finite algebraic certificates.  It uses
SymPy for exact polynomial arithmetic and Python tuples for the finite groups.
No floating-point calculation is used in a proof check.  The single displayed
numerical Bring interval is an exact rational interval obtained by bisection.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
import sys
from collections import deque
from fractions import Fraction
from pathlib import Path
from typing import Any, Callable, Iterable

import sympy as sp


class CheckFailure(AssertionError):
    pass


REPORT: list[dict[str, Any]] = []


def record(name: str, fn: Callable[[], Any]) -> None:
    try:
        detail = fn()
        REPORT.append({"name": name, "status": "PASS", "detail": detail})
        print(f"PASS  {name}")
    except Exception as exc:  # make the artifact useful as a batch checker
        REPORT.append({
            "name": name,
            "status": "FAIL",
            "detail": f"{type(exc).__name__}: {exc}",
        })
        print(f"FAIL  {name}: {exc}")


def require(cond: bool, message: str) -> None:
    if not cond:
        raise CheckFailure(message)


def check_zero(expr: sp.Expr, message: str) -> None:
    require(sp.expand(expr) == 0, f"{message}: residual = {sp.expand(expr)}")


def check_bring_sos() -> dict[str, str]:
    x, y = sp.symbols("x y")
    s4 = x**4 + x**3*y + x**2*y**2 + x*y**3 + y**4
    rhs = 3*(2*x**2 + x*y)**2 + (3*x*y + 2*y**2)**2 + 8*y**4
    check_zero(12*s4 - rhs, "sum-of-squares identity")
    check_zero((y**5 + y) - (x**5 + x) - (y-x)*(1+s4), "difference identity")
    return {
        "identity": "12*S4 = 3(2x^2+xy)^2 + (3xy+2y^2)^2 + 8y^4",
        "consequence": "h(y)-h(x)=(y-x)(1+S4) with S4>=0",
    }


def check_asymptotic_identity() -> str:
    r, y = sp.symbols("r y")
    d = r**4 + r**3*y + r**2*y**2 + r*y**3 + y**4
    check_zero(r**5-y**5-(r-y)*d, "fifth-power difference")
    return "If r^5=y^5+y and 0<y<=r, then r-y=y/D<=r/r^4=1/r^3."


def check_bring_discriminant() -> dict[str, str]:
    X, a, p, q = sp.symbols("X a p q")
    res_bring = sp.factor(sp.resultant(X**5 + X + a, 5*X**4 + 1, X))
    require(sp.expand(res_bring - (3125*a**4 + 256)) == 0,
            f"unexpected Bring resultant: {res_bring}")
    disc_general = sp.factor(sp.discriminant(X**5 + p*X + q, X))
    require(sp.expand(disc_general - (256*p**5 + 3125*q**4)) == 0,
            f"unexpected trinomial discriminant: {disc_general}")
    return {
        "bring_resultant": str(res_bring),
        "general_discriminant": str(disc_general),
        "branch_equation": "3125*a^4 + 256 = 0",
    }


def bring_coefficient(k: int) -> Fraction:
    return Fraction(math.comb(5*k, k), 4*k + 1)


def poch(q: Fraction, k: int) -> Fraction:
    out = Fraction(1)
    for j in range(k):
        out *= q + j
    return out


def check_hypergeometric_coefficients() -> dict[str, Any]:
    rows = []
    for k in range(21):
        hyper = (
            poch(Fraction(1, 5), k)
            * poch(Fraction(2, 5), k)
            * poch(Fraction(3, 5), k)
            * poch(Fraction(4, 5), k)
            / (
                poch(Fraction(1, 2), k)
                * poch(Fraction(3, 4), k)
                * poch(Fraction(5, 4), k)
                * math.factorial(k)
            )
            * Fraction(-3125, 256) ** k
        )
        target = (-1)**k * bring_coefficient(k)
        require(hyper == target, f"coefficient mismatch at k={k}: {hyper} != {target}")
        if k < 6:
            rows.append({"k": k, "coefficient": str(target)})
    k = sp.symbols("k", integer=True, nonnegative=True)
    ratio = sp.factor(
        sp.prod(5*k+i for i in range(1,6))
        / ((k+1)*sp.prod(4*k+i for i in range(2,6)))
    )
    expected = sp.factor(
        sp.Rational(3125, 256)
        * (k+sp.Rational(1,5))*(k+sp.Rational(2,5))
        * (k+sp.Rational(3,5))*(k+sp.Rational(4,5))
        / ((k+sp.Rational(1,2))*(k+sp.Rational(3,4))
           *(k+1)*(k+sp.Rational(5,4)))
    )
    check_zero(sp.together(ratio-expected).as_numer_denom()[0], "coefficient ratio")
    return {
        "checked_k": "0..20",
        "first_coefficients_for_minus_BR": rows,
        "ratio": str(ratio),
    }


def check_bring_truncation() -> dict[str, Any]:
    z = sp.symbols("z")
    max_degree = 65
    y = sum(
        sp.Rational((-1)**k * math.comb(5*k, k), 4*k+1) * z**(4*k+1)
        for k in range((max_degree-1)//4 + 1)
    )
    residual = sp.Poly(sp.expand(y**5 + y - z), z)
    bad = [(m[0], c) for m, c in residual.terms() if m[0] <= max_degree]
    require(not bad, f"nonzero coefficients through degree {max_degree}: {bad[:5]}")
    first = [str(sp.expand(y).coeff(z, n)) for n in range(1, 18)]
    return {
        "modulus": f"z^{max_degree+1}",
        "equation": "y^5+y=z",
        "coefficients_degrees_1_to_17": first,
    }


def check_scaling() -> str:
    c, u, q = sp.symbols("c u q", nonzero=True)
    p = c**4
    lhs = (c*u)**5 + p*(c*u) + q
    rhs = c**5*(u**5 + u + q/c**5)
    check_zero(sp.together(lhs-rhs), "Bring scaling")
    return "For c^4=p: x=c*u reduces x^5+p*x+q to u^5+u+q/c^5."


def check_depressed_quintic() -> dict[str, str]:
    A, B, C, D, E, F, y = sp.symbols("A B C D E F y", nonzero=True)
    x = y - B/(5*A)
    poly = A*x**5 + B*x**4 + C*x**3 + D*x**2 + E*x + F
    normalized = sp.Poly(sp.expand(poly/A), y)
    p = (5*A*C - 2*B**2)/(5*A**2)
    q = (25*A**2*D - 15*A*B*C + 4*B**3)/(25*A**3)
    r = (125*A**3*E - 50*A**2*B*D + 15*A*B**2*C - 3*B**4)/(125*A**4)
    s = (3125*A**4*F - 625*A**3*B*E + 125*A**2*B**2*D
         - 25*A*B**3*C + 4*B**5)/(3125*A**5)
    expected = y**5 + p*y**3 + q*y**2 + r*y + s
    check_zero(sp.together(normalized.as_expr()-expected).as_numer_denom()[0],
               "depressed-quintic identity")
    return {"p": str(p), "q": str(q), "r": str(r), "s": str(s)}


def check_principal_transform() -> dict[str, str]:
    S2, S3, S4, alpha = sp.symbols("S2 S3 S4 alpha")
    beta = -S2/5
    sum_y = alpha*0 + 5*beta + S2
    sum_y2 = S4 + 2*alpha*S3 + (alpha**2+2*beta)*S2 + 5*beta**2
    principal_eq = 5*S2*alpha**2 + 10*S3*alpha + 5*S4 - S2**2
    check_zero(sum_y, "first transformed power sum")
    check_zero(sp.expand(5*sum_y2-principal_eq), "second transformed power sum")
    return {
        "beta": "-S2/5",
        "alpha_equation": "5*S2*alpha^2+10*S3*alpha+5*S4-S2^2=0",
        "conclusion": "power sums 1 and 2 vanish, hence e1=e2=0",
    }


def cyclotomic_reduce(expr: sp.Expr, w: sp.Symbol) -> sp.Expr:
    phi5 = w**4+w**3+w**2+w+1
    return sp.expand(sp.rem(sp.Poly(sp.expand(expr), w), sp.Poly(phi5, w)).as_expr())


def check_de_moivre() -> dict[str, str]:
    X, u, v, w = sp.symbols("X u v w")
    roots = []
    for j in range(5):
        roots.append(w**j*u + w**((4*j) % 5)*v)
    prod = sp.Integer(1)
    for root in roots:
        prod *= X-root
    reduced = cyclotomic_reduce(sp.expand(prod), w)
    expected = X**5 - 5*u*v*X**3 + 5*u**2*v**2*X - (u**5+v**5)
    check_zero(sp.expand(reduced-expected), "de Moivre product")
    a, b, Y = sp.symbols("a b Y")
    # If Y^2+bY-a^5=0, choose u^5=Y and v=-a/u. Then uv=-a and
    # u^5+v^5=Y-a^5/Y=-b.
    quotient_identity = sp.together((Y - a**5/Y) + b)
    relation = Y**2+b*Y-a**5
    require(sp.factor(quotient_identity.as_numer_denom()[0]) == relation,
            "auxiliary quadratic reduction failed")
    return {
        "product": str(expected),
        "specialization": "uv=-a and u^5+v^5=-b gives x^5+5a*x^3+5a^2*x+b",
    }


def check_elementary_examples() -> dict[str, Any]:
    x, t = sp.symbols("x t")
    f = x**5-x**4-x+1
    fac = sp.factor(f)
    require(sp.expand(f-(x**2+1)*(x+1)*(x-1)**2) == 0, "reducible factorization")
    r = 1+t-t**2+t**3-t**4
    g = x**5-5*x**4+30*x**3-50*x**2+55*x-21
    value = sp.expand(g.subs(x, r))
    quotient, rem = sp.div(sp.Poly(value, t), sp.Poly(t**5-2, t))
    require(rem.as_expr() == 0, f"radical example remainder: {rem.as_expr()}")
    return {
        "reducible_factorization": str(fac),
        "radical_root": "1+t-t^2+t^3-t^4, t^5=2",
        "certificate_quotient_degree": int(quotient.degree()),
        "certificate_quotient": str(quotient.as_expr()),
    }


def poly_factor_degrees(expr: sp.Expr, x: sp.Symbol, modulus: int) -> list[int]:
    coeff, factors = sp.factor_list(expr, x, modulus=modulus)
    degrees: list[int] = []
    for fac, exp in factors:
        degrees.extend([sp.degree(fac, x)]*exp)
    return sorted(degrees)


def check_finite_field_and_discriminants() -> dict[str, Any]:
    x = sp.symbols("x")
    examples = [
        ("x^5-x+1", x**5-x+1, 2869, 3),
        ("x^5+x+3", x**5+x+3, 253381, 7),
    ]
    output: dict[str, Any] = {}
    for name, f, disc_expected, irreducible_prime in examples:
        disc = int(sp.discriminant(f, x))
        require(disc == disc_expected, f"{name} discriminant {disc}")
        deg2 = poly_factor_degrees(f, x, 2)
        require(deg2 == [2, 3], f"{name} mod 2 degrees {deg2}")
        degp = poly_factor_degrees(f, x, irreducible_prime)
        require(degp == [5], f"{name} mod {irreducible_prime} degrees {degp}")
        require(disc % 2 != 0 and disc % irreducible_prime != 0,
                f"bad prime divides discriminant for {name}")
        output[name] = {
            "discriminant": disc,
            "mod_2_factor_degrees": deg2,
            f"mod_{irreducible_prime}_factor_degrees": degp,
        }
    # Explicit factorization on the mod-2 side.
    mod2_product = sp.expand((x**2+x+1)*(x**3+x**2+1) - (x**5+x+1))
    require(all(int(c) % 2 == 0 for c in sp.Poly(mod2_product, x).all_coeffs()),
            "mod-2 displayed factorization failed")
    # Explicit Bézout certificate for irreducibility witness at p=3.
    f1 = x**5-x+1
    frob3 = sp.rem(x**3-x, f1, domain=sp.GF(3))
    # The certificate 1*f + (-x^2-1)*(x^3-x)=1 modulo 3.
    bez3 = sp.expand(f1 + (-x**2-1)*(x**3-x) - 1)
    require(all(int(c) % 3 == 0 for c in sp.Poly(bez3, x).all_coeffs()),
            "mod-3 Bézout certificate failed")
    output["displayed_mod2_factorization"] = "(x^2+x+1)(x^3+x^2+1)"
    output["mod3_bezout"] = "f+(-x^2-1)(x^3-x)=1"
    output["mod3_frobenius_remainder"] = str(frob3)
    return output


Perm = tuple[int, ...]


def compose(p: Perm, q: Perm) -> Perm:
    """p after q."""
    return tuple(p[q[i]] for i in range(len(p)))


def inv(p: Perm) -> Perm:
    ans = [0]*len(p)
    for i, j in enumerate(p):
        ans[j] = i
    return tuple(ans)


def parity(p: Perm) -> int:
    return sum(p[i] > p[j] for i in range(len(p)) for j in range(i+1, len(p))) % 2


def closure(gens: Iterable[Perm], n: int = 5) -> frozenset[Perm]:
    e = tuple(range(n))
    gs = set(gens)
    gs |= {inv(g) for g in list(gs)}
    H = {e}
    q: deque[Perm] = deque([e])
    while q:
        h = q.popleft()
        for g in gs:
            for z in (compose(h, g), compose(g, h)):
                if z not in H:
                    H.add(z)
                    q.append(z)
    return frozenset(H)


def commutator(g: Perm, h: Perm) -> Perm:
    return compose(compose(compose(g, h), inv(g)), inv(h))


def derived(H: frozenset[Perm]) -> frozenset[Perm]:
    gens = {commutator(g, h) for g in H for h in H}
    return closure(gens, len(next(iter(H))))


def derived_profile(H: frozenset[Perm]) -> tuple[list[int], bool]:
    """Return derived-series orders and whether the series reaches 1.

    A perfect nontrivial subgroup is reported by one repeated terminal order.
    """
    orders = [len(H)]
    while len(H) > 1:
        K = derived(H)
        orders.append(len(K))
        if K == H:
            return orders, False
        H = K
    return orders, True


def cycle_perm(n: int, cyc: list[int]) -> Perm:
    p = list(range(n))
    for i in range(len(cyc)):
        p[cyc[i]] = cyc[(i+1) % len(cyc)]
    return tuple(p)


def conjugate_subgroup(H: frozenset[Perm], s: Perm) -> frozenset[Perm]:
    si = inv(s)
    return frozenset(compose(compose(s, h), si) for h in H)


def orbit(H: frozenset[Perm], a: int) -> set[int]:
    return {h[a] for h in H}


def enumerate_subgroups(S: list[Perm]) -> set[frozenset[Perm]]:
    e = tuple(range(len(S[0])))
    subgroups: set[frozenset[Perm]] = {frozenset({e})}
    q: deque[frozenset[Perm]] = deque(subgroups)
    while q:
        H = q.popleft()
        for g in S:
            if g in H:
                continue
            K = closure(tuple(H) + (g,), len(e))
            if K not in subgroups:
                subgroups.add(K)
                q.append(K)
    return subgroups


def check_groups() -> dict[str, Any]:
    S_list = list(itertools.permutations(range(5)))
    S5 = frozenset(S_list)
    A5 = frozenset(p for p in S_list if parity(p) == 0)
    dS = derived(S5)
    dA = derived(A5)
    require(dS == A5, f"[S5,S5] order {len(dS)}")
    require(dA == A5, f"[A5,A5] order {len(dA)}")
    c5 = cycle_perm(5, [0,1,2,3,4])
    trans = cycle_perm(5, [0,1])
    generated = closure([c5, trans])
    require(generated == S5, "5-cycle and transposition did not generate S5")
    AGL = frozenset(tuple((a*i+b) % 5 for i in range(5)) for a in range(1,5) for b in range(5))
    require(len(AGL) == 20, "AGL(1,5) order")
    agl_orders, agl_solvable = derived_profile(AGL)
    require(agl_solvable and agl_orders == [20,5,1], f"AGL derived orders {agl_orders}")

    subs = enumerate_subgroups(S_list)
    transitive = [H for H in subs if len(orbit(H, 0)) == 5]
    solvable_transitive = [H for H in transitive if derived_profile(H)[1]]
    conjugates = {conjugate_subgroup(AGL, s) for s in S_list}
    for H in solvable_transitive:
        require(any(H <= C for C in conjugates),
                f"solvable transitive subgroup of order {len(H)} not in conjugate AGL")
    nonsolvable_transitive = [H for H in transitive if not derived_profile(H)[1]]
    return {
        "S5_order": len(S5),
        "A5_order": len(A5),
        "derived_S5_order": len(dS),
        "derived_A5_order": len(dA),
        "S5_derived_series": [120,60,60],
        "AGL_1_5_derived_series": agl_orders,
        "subgroups_enumerated": len(subs),
        "transitive_subgroups_as_actual_subsets": len(transitive),
        "solvable_transitive_actual_subgroups": len(solvable_transitive),
        "nonsolvable_transitive_actual_subgroups": len(nonsolvable_transitive),
        "transitive_orders": sorted({len(H) for H in transitive}),
        "solvable_transitive_orders": sorted({len(H) for H in solvable_transitive}),
        "classification_check": "every solvable transitive H<=S5 lies in a conjugate of AGL(1,5)",
    }


def check_celestial_quintic() -> dict[str, str]:
    r, R, MS, ME, w, G, eps = sp.symbols("r R M_S M_E omega G eps")
    cleared = G*MS*r**2 + eps*G*ME*(R+eps*r)**2 - w**2*r**2*(R+eps*r)**3
    expanded = sp.Poly(sp.expand(cleared.subs(eps**2, 1)), r)
    # Substitution eps^2=1 is not recursive in SymPy for higher powers; reduce eps^n manually.
    expr = sp.expand(cleared)
    expr = expr.xreplace({eps**5: eps, eps**4: 1, eps**3: eps, eps**2: 1})
    expr = sp.expand(expr)
    poly = sp.Poly(expr, r)
    require(poly.degree() == 5, f"degree {poly.degree()}")
    return {
        "cleared_equation": str(expr),
        "degree_in_r": str(poly.degree()),
        "leading_coefficient": str(poly.LC()),
    }


def check_bisection() -> dict[str, Any]:
    a = Fraction(3)
    M = math.ceil(abs(a)) + 1
    lo, hi = Fraction(-M), Fraction(M)
    def P(x: Fraction) -> Fraction:
        return x**5+x+a
    require(P(lo) <= 0 <= P(hi), "initial bracket")
    for _ in range(80):
        mid = (lo+hi)/2
        if P(mid) <= 0:
            lo = mid
        else:
            hi = mid
    require(P(lo) <= 0 <= P(hi), "final bracket")
    require(hi-lo == Fraction(2*M, 2**80), "unexpected interval width")
    return {
        "parameter_a": "3",
        "steps": 80,
        "lower": str(lo),
        "upper": str(hi),
        "width": str(hi-lo),
        "decimal_midpoint": f"{float((lo+hi)/2):.17g}",
    }


def check_generalized_four_resolvent() -> dict[str, Any]:
    """Verify MathWorld's four-resolvent expansion by cyclotomic product."""
    x, w = sp.symbols("x w")
    u1, u2, u3, u4 = sp.symbols("u1 u2 u3 u4")
    us = [None, u1, u2, u3, u4]
    prod = sp.Integer(1)
    for j in range(5):
        root = sum(w**((k*j) % 5) * us[k] for k in range(1,5))
        prod *= x-root
    red = cyclotomic_reduce(sp.expand(prod), w)
    U = u1*u4+u2*u3
    V = u1*u2**2+u2*u4**2+u3*u1**2+u4*u3**2
    W = (u1**2*u4**2+u2**2*u3**2-u1**3*u2-u2**3*u4-u3**3*u1-u4**3*u3-u1*u2*u3*u4)
    Xc = u1**3*u3*u4+u2**3*u1*u3+u3**3*u2*u4+u4**3*u1*u2
    Yc = u1*u3**2*u4**2+u2*u1**2*u3**2+u3*u2**2*u4**2+u4*u1**2*u2**2
    Z = u1**5+u2**5+u3**5+u4**5
    expected = x**5-5*U*x**3-5*V*x**2+5*W*x+(5*(Xc-Yc)-Z)
    check_zero(sp.expand(red-expected), "four-resolvent product")
    return {
        "degree": 5,
        "identity": "product over j equals x^5-5U x^3-5V x^2+5W x+5(X-Y)-Z",
        "monomials_after_expansion": len(sp.Poly(red, x,u1,u2,u3,u4).terms()),
    }



def check_differential_resolvent() -> dict[str, str]:
    """Verify the Cockle--Harley fourth-order ODE for x^5-x+a=0."""
    a, x = sp.symbols("a x")
    d = 5*x**4-1
    xp = -1/d

    def total_derivative(expr: sp.Expr) -> sp.Expr:
        return sp.factor(sp.diff(expr, a) + xp*sp.diff(expr, x))

    derivs = [x]
    for _ in range(4):
        derivs.append(total_derivative(derivs[-1]))
    ode = (
        sp.Rational(256,1155)*derivs[4]
        - sp.Rational(3125,1155)*a**4*derivs[4]
        - sp.Rational(6250,231)*a**3*derivs[3]
        - sp.Rational(4875,77)*a**2*derivs[2]
        - sp.Rational(2125,77)*a*derivs[1]
        + derivs[0]
    )
    reduced = sp.factor(sp.together(ode.subs(a, x-x**5)))
    require(reduced == 0, f"differential resolvent residual {reduced}")
    return {
        "equation": "x^5-x+a=0",
        "cleared_verification": "the ODE residual vanishes after a=x-x^5",
        "first_derivative": str(derivs[1]),
        "fourth_derivative_denominator": str(sp.denom(sp.together(derivs[4]))),
    }


def check_cyclotomic_and_young_examples() -> dict[str, Any]:
    x, t, z = sp.symbols("x t z")
    p11 = x**5+x**4-4*x**3-3*x**2+3*x+1
    subst = sp.together(p11.subs(x, z+1/z) * z**5)
    phi11 = sum(z**j for j in range(11))
    rem11 = sp.rem(sp.Poly(sp.expand(subst), z), sp.Poly(phi11, z)).as_expr()
    require(sp.expand(rem11) == 0, f"11th-root example remainder {rem11}")

    r = t-t**2+t**3-t**4
    young = x**5+20*x**3+20*x**2+30*x+10
    _, rem = sp.div(sp.Poly(sp.expand(young.subs(x, r)), t), sp.Poly(t**5-2, t))
    require(rem.as_expr() == 0, f"Paxton Young remainder {rem.as_expr()}")
    return {
        "cyclotomic_example": "if z^11=1, z!=1, then x=z+z^-1 satisfies x^5+x^4-4x^3-3x^2+3x+1=0",
        "Paxton_Young_example": "t-t^2+t^3-t^4 (t^5=2) solves x^5+20x^3+20x^2+30x+10=0",
    }

def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", type=Path, default=None, help="write JSON report")
    args = parser.parse_args()

    checks: list[tuple[str, Callable[[], Any]]] = [
        ("Bring monotonicity sum-of-squares certificate", check_bring_sos),
        ("Bring fifth-root asymptotic identity", check_asymptotic_identity),
        ("Bring/trinomial discriminant resultants", check_bring_discriminant),
        ("Bring hypergeometric coefficient identity", check_hypergeometric_coefficients),
        ("Bring formal series through degree 65", check_bring_truncation),
        ("Cockle--Harley differential resolvent", check_differential_resolvent),
        ("Scaling x^5+p*x+q to Bring form", check_scaling),
        ("General quintic depression identity", check_depressed_quintic),
        ("Quadratic principal-form power-sum reduction", check_principal_transform),
        ("de Moivre quintic cyclotomic product", check_de_moivre),
        ("General four-resolvent cyclotomic product", check_generalized_four_resolvent),
        ("Elementary solvable/reducible examples", check_elementary_examples),
        ("Cyclotomic and Paxton Young examples", check_cyclotomic_and_young_examples),
        ("Concrete Galois finite-field certificates", check_finite_field_and_discriminants),
        ("Finite group and solvable-transitive classification", check_groups),
        ("Celestial-mechanics denominator clearing", check_celestial_quintic),
        ("Exact rational bisection for BR(3)", check_bisection),
    ]
    for name, fn in checks:
        record(name, fn)

    passed = sum(row["status"] == "PASS" for row in REPORT)
    result = {
        "python": sys.version,
        "sympy": sp.__version__,
        "checks_passed": passed,
        "checks_total": len(REPORT),
        "all_passed": passed == len(REPORT),
        "checks": REPORT,
    }
    if args.json:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(json.dumps(result, indent=2, sort_keys=True, default=str) + "\n", encoding="utf-8")
    print(f"\n{passed}/{len(REPORT)} exact checks passed")
    return 0 if passed == len(REPORT) else 1


if __name__ == "__main__":
    raise SystemExit(main())
