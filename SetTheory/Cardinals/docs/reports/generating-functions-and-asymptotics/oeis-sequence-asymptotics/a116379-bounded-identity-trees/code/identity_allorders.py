#!/usr/bin/env python3
"""Finite Puiseux jets and all-fixed-order Gamma transfer, with mpmath.

Nested inputs use exact counts through N. These are high-precision numerical
stability calculations, not interval enclosures. Increasing --order generates
more fixed-order coefficients; no uniform-in-order/degree estimate is implied.
"""
import argparse
import json
from math import comb
from pathlib import Path
import mpmath as mp
from check_identity import load_terms
from formal import add, scale, mul


def elementary_jets(p, d, M):
    e = [[mp.mpf(1)] + [mp.mpf(0)]*M]
    for j in range(1, d+1):
        value = [mp.mpf(0)]*(M+1)
        for i in range(1, j+1):
            value = add(value, scale(mul(p[i], e[j-i]), (-1)**(i-1)))
        e.append(scale(value, mp.mpf(1)/j))
    return e


def gamma_corrections(alpha, K):
    """Gamma(n-alpha)/Gamma(n+1) = n**(-alpha-1)*sum(g[k]/n**k)."""
    h, g = [mp.mpf(0)]*(K+1), [mp.mpf(1)] + [mp.mpf(0)]*K
    for k in range(1, K+1):
        h[k] = ((-1)**(k+1) * (mp.bernpoly(k+1, -alpha) - mp.bernpoly(k+1, 1))
                / (k*(k+1)))
        g[k] = sum(j*h[j]*g[k-j] for j in range(1, k+1))/k
    return g


def compute(d, N=400, precision=110, R=4, route="sum", check_n=None):
    if d < 2 or N < 2 or precision < 30 or R < 0:
        raise ValueError("Require d>=2, N>=2, precision>=30, order>=0")
    if route not in ("sum", "differentiate"):
        raise ValueError("route must be sum or differentiate")
    mp.mp.dps = precision
    a = load_terms(d, N)

    def T(x):
        return mp.polyval(a[::-1], x)

    def evale(z, y):
        p = [None, y] + [T(z**i) for i in range(2, d+1)]
        e = [mp.mpf(1)]
        for j in range(1, d+1):
            e.append(sum((-1)**(i-1)*p[i]*e[j-i] for i in range(1, j+1))/j)
        return e

    rho, tau = mp.findroot(
        lambda z, y: (z*sum(evale(z, y))-y, z*sum(evale(z, y)[:-1])-1),
        (mp.mpf("0.40"), mp.mpf("1.1")), tol=mp.mpf(10)**(-precision+10))
    Fz = mp.diff(lambda z: z*sum(evale(z, tau)), rho)
    Fyy = rho*sum(evale(rho, tau)[:-2])
    if not (0 < rho < 1 and tau > 1 and Fz > 0 and Fyy > 0):
        raise ArithmeticError("Computed root does not satisfy characteristic sign checks")
    M = 2*R+2
    z = [rho, mp.mpf(0), -rho] + [mp.mpf(0)]*(M-2)
    p = [None, None]
    for i in range(2, d+1):
        v = [mp.mpf(0)]*(M+1)
        if route == "sum":
            for q in range(M//2+1):
                v[2*q] = (-1)**q * sum(
                    mp.mpf(a[n])*rho**(i*n)*comb(i*n, q)
                    for n in range(max(1, (q+i-1)//i), len(a)))
        else:
            # Independent nested-input route: automatic numerical Taylor
            # differentiation of the composed finite polynomial in s=t**2.
            for q, coefficient in enumerate(mp.taylor(
                    lambda s: T((rho*(1-s))**i), 0, M//2)):
                v[2*q] = coefficient
        p.append(v)

    def G(c):
        p[1] = c
        E = elementary_jets(p, d, M)
        return add(c, scale(mul(z, [sum(e[k] for e in E) for k in range(M+1)]), -1))

    c = [tau, -mp.sqrt(2*rho*Fz/Fyy)] + [mp.mpf(0)]*(M-1)
    slope_errors = []
    for k in range(2, 2*R+2):
        c[k] = 0
        v0 = G(c)[k+1]
        c[k] = 1
        slope = G(c)[k+1]-v0
        slope_errors.append(abs(slope + Fyy*c[1]))
        c[k] = -v0/slope
    D = [sum(c[2*ell+1]/c[1] * mp.gamma(-mp.mpf(".5")) /
             mp.gamma(-ell-mp.mpf(".5")) *
             gamma_corrections(ell+mp.mpf(".5"), j-ell)[j-ell]
             for ell in range(j+1)) for j in range(R+1)]
    C = c[1]/mp.gamma(-mp.mpf(".5"))
    checks = []
    for n in (check_n if check_n is not None else [50, 100, 200, 400]):
        if not 1 <= n <= N:
            continue
        carrier = C*rho**(-n)*mp.mpf(n)**(-mp.mpf("1.5"))
        residual = [mp.mpf(a[n])/(carrier*sum(D[k]/mp.mpf(n)**k
                    for k in range(j+1)))-1 for j in range(R+1)]
        checks.append({"n": n, "relative_residual_by_order": list(map(str, residual)),
                       "residual_sign_by_order": [int(mp.sign(x)) for x in residual]})
    return {"d": d, "N": N, "precision": precision, "R": R, "route": route,
            "rho": str(rho), "tau": str(tau), "C": str(C),
            "Fz": str(Fz), "Fyy": str(Fyy),
            "puiseux": list(map(str, c[:2*R+2])), "corrections": list(map(str, D)),
            "jet_residual_max": str(max(map(abs, G(c)))),
            "linear_slope_check_max": str(max(slope_errors, default=0)),
            "residual_convention": "exact_count / truncated_asymptotic - 1",
            "checks": checks}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--degrees", nargs="+", type=int, default=[3, 4])
    parser.add_argument("--N", type=int, default=400)
    parser.add_argument("--precision", type=int, default=110)
    parser.add_argument("--order", type=int, default=4)
    parser.add_argument("--route", choices=["sum", "differentiate"], default="sum")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    results = [compute(d, args.N, args.precision, args.order, args.route)
               for d in args.degrees]
    for row in results:
        print(f"d={row['d']} rho={row['rho']} C={row['C']}")
        print("D=" + json.dumps(row["corrections"]))
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(results, indent=2) + "\n")


if __name__ == "__main__":
    main()
