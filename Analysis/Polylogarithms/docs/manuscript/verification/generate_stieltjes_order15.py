"""Reproduce the order-15 certificate by exact subresultant construction.

This optional generator uses the real Cayley recurrence; the companion
checker independently reconstructs the original-color numerators and uses
no elimination. Its strict output contains exact data only.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import sympy as s

from check_stieltjes_order15 import SCOPE, require

HERE = Path(__file__).resolve().parent
b, t, X, Y = s.symbols("b t X Y", real=True)


def primitive(poly):
    return poly.clear_denoms()[1].primitive()[1]


def add(U, V):
    return U[0]+V[0], U[1]+V[1]


def mul(U, V):
    products = [u*v for u in U for v in V]
    return min(products), max(products)


def reciprocal(U):
    require(U[0]*U[1] > 0, "Denominator interval includes zero")
    return min(1/U[0], 1/U[1]), max(1/U[0], 1/U[1])


def evaluate(poly, interval):
    result = (s.Rational(0), s.Rational(0))
    for coefficient in poly.all_coeffs():
        result = add(mul(result, interval), (coefficient, coefficient))
    return result


def outward_decimal(interval, digits):
    scale = s.Integer(10)**digits
    return s.floor(interval[0]*scale)/scale, s.ceiling(interval[1]*scale)/scale


def generate():
    B = [s.Integer(1)]
    for _ in range(16):
        B.append(s.expand((b+s.I*t/2)*B[-1] + s.I*(1+t*t)*s.diff(B[-1], t)/2))

    def squared(expression):
        poly = s.Poly(s.expand(expression), b, t)
        require(all(i % 2 == j % 2 == 0 for (i, j), _ in poly.terms()),
                "Cayley parity failed")
        return s.Poly(sum(c*X**(i//2)*Y**(j//2) for (i, j), c in poly.terms()),
                      X, Y, domain=s.QQ)

    R = [squared(s.re(B[k])/(b if k % 2 else 1)) for k in range(17)]
    I = [squared(s.im(B[k])/(t*(b if k % 2 == 0 else 1))) for k in range(17)]
    rp, ip = primitive(R[15]), primitive(I[15])
    print("Constructing exact subresultants", flush=True)
    sequence = s.subresultants(rp.as_expr(), ip.as_expr(), X)
    require([s.degree(poly, X) for poly in sequence] == [7, 7, 6, 5, 4, 3, 2, 1, 0],
            "Unexpected subresultant degree sequence")
    H = s.Poly(638512875*Y**7 + 2766889125*Y**6 + 4838508675*Y**5
               + 4339860525*Y**4 + 2087700615*Y**3 + 507350025*Y**2
               + 50307087*Y + 929569, Y, domain=s.QQ)
    quotient, remainder = s.Poly(sequence[-1], Y, domain=s.QQ).div(H)
    require(remainder.is_zero, "Resultant not divisible by displayed H7")
    P = primitive(quotient)
    if P.LC() < 0:
        P = -P
    require(P.degree() == 42 and P.TC() < 0, "Unexpected root-polynomial degree or orientation")
    signs = [s.sign(c) for c in P.all_coeffs() if c]
    require(sum(x != y for x, y in zip(signs, signs[1:])) == 1
            and P.eval(1) < 0 < P.eval(2), "Positive-root isolation failed")
    linear = s.Poly(sequence[-2], X)
    numerator, denominator = s.fraction(s.cancel(-linear.nth(0)/linear.nth(1)))
    N = s.Poly(numerator, Y, domain=s.QQ).rem(P)
    D = s.Poly(denominator, Y, domain=s.QQ).rem(P)
    require(N.degree() == 37 and D.degree() == 36, "Unexpected rational-lift degrees")

    def at_rational_mod(poly):
        px = s.Poly(poly.as_expr(), X)
        require(px.degree() == 7, "Unexpected homogenization degree")
        ns, ds = [s.Poly(1, Y, domain=s.QQ)], [s.Poly(1, Y, domain=s.QQ)]
        for _ in range(7):
            ns.append((ns[-1]*N).rem(P))
            ds.append((ds[-1]*D).rem(P))
        residue = s.Poly(0, Y, domain=s.QQ)
        for j in range(8):
            residue = (residue+s.Poly(px.nth(j), Y)*ns[j]*ds[7-j]).rem(P)
        return residue

    require(at_rational_mod(rp).is_zero and at_rational_mod(ip).is_zero,
            "Rational lift does not solve both tail equations")
    lo, hi = s.Rational(1), s.Rational(2)
    for _ in range(320):
        midpoint = (lo+hi)/2
        value = P.eval(midpoint)
        require(value != 0, "Unexpected exact dyadic root; update isolation convention")
        if value < 0:
            lo = midpoint
        else:
            hi = midpoint
    yint = (lo, hi)
    dint = evaluate(D, yint)
    xint = outward_decimal(mul(evaluate(N, yint), reciprocal(dint)), 24)
    ybox = outward_decimal(yint, 24)
    require(xint[0] > s.Rational(1, 4) and ybox[0] > 0, "Cayley domain failed")

    def evaluate_xy(poly):
        result = (s.Rational(0), s.Rational(0))
        for coefficient in s.Poly(poly.as_expr(), X).all_coeffs():
            result = add(mul(result, xint), evaluate(s.Poly(coefficient, Y), ybox))
        return result

    adjacent = {}
    for k in (14, 16):
        rint = outward_decimal(evaluate_xy(R[k]), 12)
        iint = outward_decimal(evaluate_xy(I[k]), 12)
        require(rint[0]*rint[1] > 0 or iint[0]*iint[1] > 0,
                f"Could not exclude zero in adjacent tail {k}")
        adjacent[str(k)] = {"R_interval": list(map(str, rint)),
                            "I_interval": list(map(str, iint))}
    return {"schema_version": 1, "order": 15, "scope": SCOPE,
            "P": str(P.as_expr()), "N": str(N.as_expr()), "D": str(D.as_expr()),
            "R15": str(rp.as_expr()), "I15": str(ip.as_expr()),
            "Y_isolating_interval": list(map(str, yint)),
            "Y_enclosure": list(map(str, ybox)), "X_enclosure": list(map(str, xint)),
            "D_enclosure": list(map(str, outward_decimal(dint, 12))),
            "adjacent_tails": adjacent}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=HERE/"stieltjes-order15-certificate.json")
    args = parser.parse_args()
    certificate = generate()
    args.output.write_text(json.dumps(certificate, indent=2)+"\n", encoding="utf-8")
    print("PASS: exact resultant quotient, rational lift, and adjacent-tail intervals", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
