#!/usr/bin/env python3
"""Optional positive-sector quadrature diagnostics (mpmath), never a proof.

The reported working precision is not a rigorous quadrature error bound.
The parameter n is cap+1, not word length. Fixed m is the Taylor-sector index.
"""
from __future__ import annotations

import argparse
import json
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--n", type=int, nargs="+", default=[101])
    parser.add_argument("--m", type=int, nargs="+", default=[1, 2, 3])
    parser.add_argument("--dps", type=int, default=50)
    args = parser.parse_args()
    if any(n < 3 for n in args.n):
        parser.error("every n must be an integer >= 3")
    if any(m < 1 for m in args.m):
        parser.error("every m must be an integer >= 1")
    if args.dps < 25:
        parser.error("use at least 25 decimal digits")
    try:
        import mpmath as mp
    except ImportError:
        print("Optional numerical sector diagnostics require mpmath.", file=sys.stderr)
        return 2
    mp.mp.dps = args.dps
    rows = []
    for n in args.n:
        for m in args.m:
            base = (mp.mpf(m)/(m+1))**m
            lead = ((2*mp.pi)**(mp.mpf(1-m)/2)*mp.mpf(m)**mp.mpf("1.5") *
                    (m+1)**(m-2)*mp.mpf(n)**(mp.mpf(3-m)/2)*base**n)

            def integrand(x):
                if not x:
                    return mp.mpf(0)
                gamma_cdf = mp.gammainc(n, 0, x)/mp.gamma(n)
                t = mp.exp(-x)
                zz = -mp.expm1(-x)
                if x < 1:
                    derivative_factor = mp.hyper([1, m+1], [m+2], zz)/(m+1)
                else:
                    derivative_factor = (x-sum(zz**j/j for j in range(1, m+1)))/zz**(m+1)
                return t*gamma_cdf**m*derivative_factor/lead

            center = mp.mpf(m)*n/(m+1)
            width = mp.sqrt(m*n)/(m+1)
            cuts = sorted(set([mp.mpf(0), max(mp.mpf(1), center-8*width),
                               center-3*width, center, center+3*width,
                               center+8*width, mp.mpf(n), 2*mp.mpf(n)]))
            ratio = mp.quad(integrand, [value for value in cuts if value >= 0]+[mp.inf])
            kappa = (mp.mpf(23*m)/12 + mp.mpf(13)/(12*m) - mp.mpf(m*m*(m+1))/2
                     - mp.mpf(m+1)*mp.harmonic(m)/m)
            row = {"n_cap_plus_one": n, "m_sector_index": m,
                   "sector_over_leading_term": str(ratio),
                   "n_times_ratio_minus_one": str(n*(ratio-1)), "kappa": str(kappa)}
            if m == 1:
                exact_linear_approximation = n*mp.zeta(n+1, 2)
                row["relative_difference_from_linear_hurwitz_zeta_evaluation"] = str(
                    (ratio*lead-exact_linear_approximation)/exact_linear_approximation)
            if m == 2:
                row["n_squared_times_second_correction"] = str(n*n*(ratio-1-kappa/n))
                row["c_2_2"] = str(mp.mpf(5437)/128)
            rows.append(row)
    print(json.dumps({"role": "approximate diagnostics; not interval-certified and not proof",
                      "mpmath_version": mp.__version__, "decimal_precision": args.dps,
                      "rows": rows}, indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
