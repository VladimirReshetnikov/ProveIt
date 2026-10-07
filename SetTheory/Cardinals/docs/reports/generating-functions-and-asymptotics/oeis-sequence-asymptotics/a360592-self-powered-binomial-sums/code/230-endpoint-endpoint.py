#!/usr/bin/env python3
"""Report230: exact, self-contained endpoint-family coefficient generators.

Only the Python standard library is needed. A polynomial is a sparse dictionary
{nonnegative_degree: Fraction}; zero coefficients are omitted. Coefficients are
ascending in every text/JSON output. Public generators validate their arguments
with exceptions (never assertions), including under python -O.

This implements fixed-order algebraic expansions, not a convergence claim or a
certified finite-n error bound. Numerical diagnostics live in diagnostics.py.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as F
from functools import lru_cache
import json
from math import comb
import sys

MAX_P = 64
MAX_ORDER = 16
MAX_FRACTIONAL_ORDER = 32
MAX_CRITICAL_ORDER = 8
MAX_CUMULANT = 16
MAX_EXACT_N = 20000


def _integer(name, value, low, high):
    if type(value) is not int:
        raise TypeError(f"{name} must be an int, not {type(value).__name__}")
    if not low <= value <= high:
        raise ValueError(f"{name} must be between {low} and {high}, inclusive")
    return value


def _clean(a):
    return {k: F(v) for k, v in a.items() if v}


def _add(a, b):
    out = dict(a)
    for k, v in b.items():
        out[k] = out.get(k, F(0)) + v
    return _clean(out)


def _scale(a, c):
    return _clean({k: v*c for k, v in a.items()})


def _mul(a, b):
    out = {}
    for i, x in a.items():
        for j, y in b.items():
            out[i+j] = out.get(i+j, F(0)) + x*y
    return _clean(out)


def _shift(a, d):
    return {k+d: v for k, v in a.items()}


@lru_cache(maxsize=MAX_ORDER+2)
def _power_sum(j):
    """sum(h**j, h=0,...,r-1), with immutable cached coefficients."""
    if j == 0:
        return ((1, F(1)),)
    out = {j+1: F(1)}
    for k in range(j):
        out = _add(out, _scale(dict(_power_sum(k)), -comb(j+1, k)))
    return tuple(sorted(_scale(out, F(1, j+1)).items()))


def defect_polynomials(p, order):
    """Return [D_0=0,D_1,...,D_order], for integer p>=1.

    Delta_n(r) = sum D_j(r)/n**j is the formal logarithmic expansion.
    p=1 is valid here, but requires critical_coefficients for averaging.
    """
    _integer("p", p, 1, MAX_P)
    _integer("order", order, 0, MAX_ORDER)
    q = p+1
    result = [{}]
    for j in range(1, order+1):
        out = {j+1: F(p**j, q)*(F(1, j)-F(p*p, j+1))}
        for a in range(1, j+1):
            scalar = F(comb(j, a)*p**(j-a)*(-q)**a, j)
            out = _add(out, _scale(_shift(dict(_power_sum(a)), j-a), scalar))
        result.append(_scale(out, (-1)**(j+1)))
    return result


@lru_cache(maxsize=2*MAX_ORDER+2)
def _touchard(d):
    if d == 0:
        return ((0, F(1)),)
    prev = dict(_touchard(d-1))
    out = _shift(prev, 1)
    out = _add(out, {k: k*v for k, v in prev.items() if k})
    return tuple(sorted(out.items()))


def touchard(d):
    """Return T_d(z)=E[X**d] for X~Poisson(z), exactly."""
    _integer("degree", d, 0, 2*MAX_ORDER)
    return dict(_touchard(d))


def coefficient_arrays(p, order):
    """Return (D,H,U), indexed 0..order; U_j(z)=E[H_j(Pois(z))]."""
    _integer("p", p, 2, MAX_P)
    _integer("order", order, 0, MAX_ORDER)
    D = defect_polynomials(p, order)
    H = [{0: F(1)}]
    for j in range(1, order+1):
        v = {}
        for s in range(1, j+1):
            v = _add(v, _scale(_mul(D[s], H[j-s]), F(s, j)))
        H.append(v)
    U = []
    for h in H:
        v = {}
        for d, a in h.items():
            v = _add(v, _scale(dict(_touchard(d)), a))
        U.append(v)
    return D, H, U


def fractional_coefficients(p, order):
    """Return C_0(c),...,C_order(c) in t=n**(-1/(p+1)), p>=2.

    c=exp(p*p/(p+1))*(p+1)**(-1/(p+1)). The normalized count is
    sum C_k(c)*t**k + O(t**(order+1)) for fixed p and order.
    """
    _integer("p", p, 2, MAX_P)
    _integer("order", order, 0, MAX_FRACTIONAL_ORDER)
    J = order//(p-1)
    _integer("required H order", J, 0, MAX_ORDER)
    U = coefficient_arrays(p, J)[2]
    C = [{} for _ in range(order+1)]
    for j, u in enumerate(U):
        for d, v in u.items():
            k = (p+1)*j-d
            if 0 <= k <= order:
                C[k][d] = C[k].get(d, F(0)) + v
    return [_clean(c) for c in C]


def marked_coefficients(p, order, cumulant=2):
    """Return (L,theta**cumulant L), for p>=2, theta=z*d/dz.

    L_0=0. log R has algebraic coefficients L_j(lambda)/n**j.
    The h-th cumulant is lambda + sum theta**h L_j(lambda)/n**j.
    These are algebraic coefficients; no secondary exponential sector is claimed.
    """
    _integer("p", p, 2, MAX_P)
    _integer("order", order, 0, MAX_ORDER)
    _integer("cumulant", cumulant, 1, MAX_CUMULANT)
    U = coefficient_arrays(p, order)[2]
    L = [{}]
    for j in range(1, order+1):
        v = dict(U[j])
        for k in range(1, j):
            v = _add(v, _scale(_mul(L[k], U[j-k]), -F(k, j)))
        L.append(v)
    thetaL = [{d: a*d**cumulant for d, a in ell.items() if d} for ell in L]
    return L, thetaL


@lru_cache(maxsize=2048)
def _associated(d, k):
    if d == k == 0:
        return 1
    if d < 0 or k <= 0 or 2*k > d:
        return 0
    return k*_associated(d-1, k)+(d-1)*_associated(d-2, k-1)


def _weighted_mul(a, b, weight):
    # Keys are (power of t, power of u, power of c). c has weight zero.
    out = {}
    for (i, j, k), x in a.items():
        for (ii, jj, kk), y in b.items():
            if 2*(i+ii)+j+jj <= weight:
                key = (i+ii, j+jj, k+kk)
                out[key] = out.get(key, F(0))+x*y
    return _clean(out)


def critical_coefficients(order):
    """Return p=1 coefficients C_0(c),...,C_order(c), c=sqrt(e/2).

    Normalization is M=(1/2)*(n/2)**(n/2)*exp(c*sqrt(n)-3*e/8).
    Weighted Taylor degree 2*order+1 is essential to the proved remainder.
    """
    _integer("order", order, 0, MAX_CRITICAL_ORDER)
    weight = 2*order+1
    V = {(0, 0, 2): F(3, 4)}
    for j, dpoly in enumerate(defect_polynomials(1, order+1)):
        for d, a in dpoly.items():
            i = 2*j-d
            for b in range(d+1):
                if 2*i+b <= weight:
                    key = (i, b, d-b)
                    V[key] = V.get(key, F(0))+a*comb(d, b)
    V = _clean(V)
    if any(i < 0 or 2*i+j <= 0 for i, j, _ in V):
        raise ArithmeticError("critical exponent has nonpositive weight")
    term = {(0, 0, 0): F(1)}
    E = dict(term)
    for m in range(1, weight+1):
        term = _scale(_weighted_mul(term, V, weight), F(1, m))
        E = _add(E, term)
    C = [{} for _ in range(order+1)]
    for (i, d, a), v in E.items():
        for k in range(d//2+1):
            power = i+d-k
            b = _associated(d, k)
            if b and power <= order:
                C[power][a+k] = C[power].get(a+k, F(0))+v*b
    return [_clean(c) for c in C]


def exact_count(p, n):
    """Compute a_p(n) as a Python integer. n=0 gives 1 without using 0**0.

    The hard n cap prevents accidental huge-integer workloads. It is a resource
    policy of this program, not a mathematical restriction. Near the cap a call
    may take minutes, depending on hardware; diagnostics default to n<=300.
    """
    _integer("p", p, 1, MAX_P)
    _integer("n", n, 0, MAX_EXACT_N)
    return 1+sum(pow(n-p*k, p*k)*comb(n-p*k, k)
                 for k in range(1, n//(p+1)+1))


def polynomial_text(poly, variable="c"):
    """Format one exact polynomial; used for deterministic human-readable output."""
    if not poly:
        return "0"
    terms = []
    for d, a in sorted(poly.items()):
        terms.append(str(a) if d == 0 else f"({a})*{variable}^{d}")
    return " + ".join(terms).replace("+ (-", "- (")


def polynomial_json(poly):
    return {str(d): str(a) for d, a in sorted(poly.items())}


def _main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="command", required=True)
    for name, helptext in (("coefficients", "p>=2 fractional coefficients"),
                           ("arrays", "D/H/Touchard U polynomials in n^-j"),
                           ("marked", "marked log-normalizer and cumulant coefficients")):
        s = sub.add_parser(name, help=helptext)
        s.add_argument("--p", type=int, default=2)
        s.add_argument("--order", type=int, default=4 if name != "marked" else 3)
        s.add_argument("--json", action="store_true")
        if name == "marked":
            s.add_argument("--cumulant", type=int, default=2)
    s = sub.add_parser("critical", help="p=1 weighted centered generator")
    s.add_argument("--order", type=int, default=4)
    s.add_argument("--json", action="store_true")
    s = sub.add_parser("count", help="exact finite integer sum; large n can be slow")
    s.add_argument("--p", type=int, default=2)
    s.add_argument("--n", type=int, required=True)
    s.add_argument("--json", action="store_true")
    args = parser.parse_args()
    try:
        if args.command == "count":
            value = exact_count(args.p, args.n)
            # Local CLI output only; never disable Python's conversion safeguard.
            if hasattr(sys, "set_int_max_str_digits"):
                sys.set_int_max_str_digits(100000)
            print(json.dumps({"p": args.p, "n": args.n, "a": str(value)}, indent=2)
                  if args.json else value)
            return
        if args.command == "critical":
            groups = {"C": critical_coefficients(args.order)}
            variable = "c"
            context = {"p": 1, "order": args.order, "c": "sqrt(e/2)", "t": "n^(-1/2)"}
        else:
            context = {"p": args.p, "order": args.order}
            if args.command == "coefficients":
                groups = {"C": fractional_coefficients(args.p, args.order)}
                variable = "c"
                context.update(c=f"exp({args.p**2}/{args.p+1})*{args.p+1}^(-1/{args.p+1})", t=f"n^(-1/{args.p+1})")
            elif args.command == "arrays":
                D, H, U = coefficient_arrays(args.p, args.order)
                groups = {"D": D, "H": H, "U": U}
                variable = "r (D,H) or z (U)"
            else:
                L, cum = marked_coefficients(args.p, args.order, args.cumulant)
                groups = {"L": L, f"theta^{args.cumulant}L": cum}
                variable = "z"
                context["cumulant"] = args.cumulant
        if args.json:
            context["polynomial_encoding"] = "degree: exact rational string; omitted coefficients are zero"
            context.update({name: [polynomial_json(p) for p in polys] for name, polys in groups.items()})
            print(json.dumps(context, indent=2))
        else:
            print("; ".join(f"{k}={v}" for k, v in context.items()))
            for name, polys in groups.items():
                for j, poly in enumerate(polys):
                    var = ("r" if name in ("D", "H") else "z") if args.command == "arrays" else variable
                    print(f"{name}_{j} = {polynomial_text(poly, var)}")
    except (ValueError, TypeError) as exc:
        parser.error(str(exc))


if __name__ == "__main__":
    _main()
