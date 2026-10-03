#!/usr/bin/env python3
"""Specified finite-model inverses: Lambert carrier, recursive and pure-log.

Model: M_R(x)=C*exp(lambda*x)*x**(-3/2)*sum_{j=0}^R D[j]/x**j.
The inverse expansion order K may exceed R: D[j]=0 for every j>R.
This does not claim exact rounding for the discrete integer threshold.
"""
import argparse
import json
from pathlib import Path
import mpmath as mp
from check_identity import DATA, load_terms
from formal import add, scale, mul, logpoly, invpoly, Polynomial


def model_coefficients(D, R, K):
    if R < 0 or K < 0 or len(D) <= R or D[0] != 1:
        raise ValueError("Require R,K>=0 and coefficients D[0]=1 through D[R]")
    return [D[j] if j <= R else mp.mpf(0) for j in range(K+1)]


def inverse_coefficients(lam, D, R, K):
    """E[1:K+1] in x=x0+sum E[k]/x0**k, for the specified R-model."""
    D = model_coefficients(D, R, K)
    one, e = [mp.mpf(1)]+[mp.mpf(0)]*K, [mp.mpf(0)]*(K+1)
    u = [mp.mpf(0)]*(K+1)
    if K:
        u[1] = 1

    def equation(e):
        v = add(one, mul(u, e))
        w = mul(u, invpoly(v))
        power, q = one.copy(), one.copy()
        for j in range(1, K+1):
            power = mul(power, w)
            q = add(q, scale(power, D[j]))
        return add(add(scale(e, lam), scale(logpoly(v), -mp.mpf("1.5"))), logpoly(q))

    for k in range(1, K+1):
        e[k] = -equation(e)[k]/lam
    return e


def pure_log_polynomials(lam, D, R, K):
    """P[k](h) in lambda*x=L+p*h+sum P[k](h)/L**k; h=log(L/lambda).

    Returns [P1,...,PK], each represented in ascending powers of h. The
    polynomial recursion itself uses no Lambert-W or root-finding calls.
    """
    D = model_coefficients(D, R, K)
    p = mp.mpf("1.5")
    one = [Polynomial([mp.mpf(1)])] + [Polynomial([mp.mpf(0)]) for _ in range(K)]
    u = [Polynomial([mp.mpf(0)]) for _ in range(K+1)]
    if K:
        u[1] = Polynomial([mp.mpf(1)])
    s = [Polynomial([mp.mpf(0), p])] + [Polynomial([mp.mpf(0)]) for _ in range(K)]
    for k in range(1, K+1):
        v = add(one, mul(u, s))
        w = scale(mul(u, invpoly(v)), lam)
        power, q = one.copy(), one.copy()
        for j in range(1, K+1):
            power = mul(power, w)
            q = add(q, scale(power, D[j]))
        s[k] = scale(logpoly(v), p)[k] - logpoly(q)[k]
    return [s[k] for k in range(1, K+1)]


def compute(src, R=4, K=4, precision=90, check_n=None):
    mp.mp.dps = precision
    d, rho, C = src["d"], mp.mpf(src["rho"]), mp.mpf(src["C"])
    D = list(map(mp.mpf, src["corrections"]))
    if len(D) <= R:
        raise ValueError("Source contains fewer corrections than requested model order")
    D = D[:R+1]  # The specified model never silently acquires higher terms.
    lam, p = -mp.log(rho), mp.mpf("1.5")
    e = inverse_coefficients(lam, D, R, K)
    polynomials = pure_log_polynomials(lam, D, R, K)
    ns = check_n if check_n is not None else [50, 100, 200, 400]
    a, checks = load_terms(d, max(ns, default=1)), []

    def logmodel(x):
        q = sum(D[j]*x**(-j) for j in range(R+1))
        if x <= 0 or q <= 0:
            raise ArithmeticError("Outside positive large-x model branch")
        return mp.log(C)+lam*x-p*mp.log(x)+mp.log(q)

    for n in ns:
        y = mp.mpf(a[n])
        argument = -lam/p*(C/y)**(1/p)
        if not -1/mp.e < argument < 0:
            raise ArithmeticError("Lambert carrier has no selected large real branch")
        x0 = mp.re(-p/lam*mp.lambertw(argument, -1))
        xm = mp.findroot(lambda x: logmodel(x)-mp.log(y), x0)
        derivative = mp.diff(logmodel, xm)
        if derivative <= 0:
            raise ArithmeticError("Computed inverse is not on the increasing model branch")
        lambert = [x0 + sum(e[k]*x0**(-k) for k in range(1, r+1))
                   for r in range(K+1)]
        L = mp.log(y/C)
        if L <= 0:
            raise ArithmeticError("Pure-log expansion needs positive L")
        h = mp.log(L/lam)
        logs = [(L+p*h+sum(polynomials[k-1].evaluate(h)*L**(-k)
                          for k in range(1, r+1)))/lam for r in range(K+1)]
        checks.append({"n": n, "model_inverse_minus_exact_n": str(xm-n),
            "model_inverse_residual_sign": int(mp.sign(xm-n)),
            "model_log_equation_residual": str(logmodel(xm)-mp.log(y)),
            "model_log_derivative": str(derivative),
            "inverse_series_minus_model_by_order": [str(x-xm) for x in lambert],
            "inverse_series_minus_exact_n_by_order": [str(x-n) for x in lambert],
            "inverse_series_residual_sign_by_order": [int(mp.sign(x-n)) for x in lambert],
            "pure_log_minus_model_by_order": [str(x-xm) for x in logs],
            "pure_log_minus_exact_n_by_order": [str(x-n) for x in logs]})
    return {"d": d, "model_order": R, "inverse_order": K, "precision": precision,
            "lambda": str(lam), "model_corrections": list(map(str, D)),
            "zero_extension": "D_j = 0 for every j > model_order",
            "inverse_coefficients": list(map(str, e)),
            "pure_log_polynomials_ascending_h": [list(map(str, q.coefficients)) for q in polynomials],
            "residual_convention": "inverse approximation minus model inverse or exact n, as labeled",
            "checks": checks}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, default=DATA/"identity-allorders-checks.json")
    parser.add_argument("--degrees", type=int, nargs="+", default=[3, 4])
    parser.add_argument("--model-order", type=int, default=4)
    parser.add_argument("--inverse-order", type=int, default=4)
    parser.add_argument("--precision", type=int, default=90)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    source = json.loads(args.input.read_text())
    rows = []
    for d in args.degrees:
        candidates = [x for x in source if x["d"] == d and x["R"] >= args.model_order]
        if not candidates:
            parser.error(f"No adequate coefficient record for d={d}")
        src = max(candidates, key=lambda x: (x["N"], x["precision"]))
        row = compute(src, args.model_order, args.inverse_order, args.precision)
        rows.append(row)
        print(f"d={d} R={args.model_order} K={args.inverse_order} E={row['inverse_coefficients']}")
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(rows, indent=2) + "\n")


if __name__ == "__main__":
    main()
