#!/usr/bin/env python3
"""Optional mpmath diagnostics; never called by the exact verification runner.

Approximate quadrature and finite differences are not rigorous error bounds,
interval certificates, asymptotic proofs, or evidence of an error rate in n.
"""
from __future__ import annotations

import argparse
import json
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--r", type=int, nargs="+", choices=range(2, 7), default=list(range(2, 7)))
    parser.add_argument("--dps", type=int, default=35)
    parser.add_argument("--drift", action="store_true", help="also print finite-difference drift residuals at w=0.2,1,4,100")
    args = parser.parse_args()
    if args.dps < 25:
        parser.error("use at least 25 decimal digits")
    try:
        import mpmath as m
    except ImportError:
        print("Optional diagnostic requires mpmath; the exact suite has no third-party dependencies.", file=sys.stderr)
        return 2
    m.mp.dps = args.dps

    def g(t):
        h = t-1
        if abs(h) < m.mpf("1e-8"):
            return sum((-h)**k/(k+1) for k in range(16))
        return m.log(t)/h

    def gp(t):
        h = t-1
        if abs(h) < m.mpf("1e-8"):
            return sum((-1)**k*k*h**(k-1)/(k+1) for k in range(1, 17))
        return (1-1/t-m.log(t))/h**2

    def E(j, w):
        return sum(w**k/m.factorial(k) for k in range(j+1))

    def X(r, j, w, mu):
        return -mu*E(j, w)*m.quad(
            lambda s: gp(E(r, w+s))*s**(r-j)/m.factorial(r-j), [0, 1, 10, m.inf])

    report = {"role": "approximate diagnostics only; not a proof or interval certificate",
              "mpmath_version": m.__version__, "decimal_precision": args.dps, "rows": []}
    for r in args.r:
        J = m.quad(lambda w: g(E(r, w)), [0, 1, 10, m.inf])
        mu = 1/J
        b = [X(r, j, m.mpf(0), mu) for j in range(1, r+1)]
        multiplicities = [b[r-k-1] for k in range(1, r)]
        multiplicities += [(1-sum((r-j)*b[j-1] for j in range(1, r)))/r]
        row = {"r": r, "J": str(J), "mu": str(mu), "b": list(map(str, b)),
               "multiplicities": list(map(str, multiplicities)),
               "distinct": str(sum(multiplicities)), "ascents": str(sum(multiplicities)+b[-1]),
               "absolute_sum_b_minus_mu": str(abs(sum(b)-mu))}
        if r == 2:
            row["absolute_mu_minus_8_over_3_pi_squared"] = str(abs(mu-8/(3*m.pi**2)))
        if args.drift:
            residuals = []
            for w in map(m.mpf, ["0.2", "1", "4", "100"]):
                u = [E(j, w) for j in range(r+1)]
                x = [X(r, j, w, mu) for j in range(1, r+1)]
                p = [u[j-1]/u[j]*x[j-1]/(mu*g(u[-1])) for j in range(1, r+1)]
                ascent = -u[-1]*gp(u[-1])/g(u[-1])
                h = m.mpf("1e-7")
                derivative = [(X(r, j, w+h, mu)-X(r, j, w-h, mu))/(2*h)/(-mu*g(u[-1]))
                              for j in range(1, r+1)]
                target = [p[j]-p[j-1] for j in range(1, r)] + [ascent-p[-1]]
                residuals.append({"w": str(w), "finite_difference_step": str(h),
                                  "maximum_absolute_drift_residual": str(max(abs(a-bb) for a, bb in zip(derivative, target))),
                                  "absolute_sum_p_minus_one": str(abs(sum(p)-1)),
                                  "minimum_p": str(min(p)), "ascent_fraction": str(ascent)})
            row["finite_difference_diagnostics"] = residuals
        report["rows"].append(row)
    print(json.dumps(report, indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
