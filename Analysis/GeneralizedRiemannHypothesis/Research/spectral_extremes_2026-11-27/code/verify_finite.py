#!/usr/bin/env python3
"""Independent finite check for the conditional maximum of weighted exponentials.

Two evaluations are compared:
  (1) exact finite inclusion-exclusion, with a hypoexponential CDF;
  (2) numerical Bromwich inversion (de Hoog algorithm) of the Laplace
      transform of the capped sum probability.

The second method does not expand the product or call inclusion-exclusion.
Both methods use arbitrary precision mpmath arithmetic. This is a numerical
consistency check, not an interval certificate or proof of an asymptotic law.
Only theta=1 and finite spectra gamma_j=j are tested.
"""
from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path
import mpmath as mp


def hypoexp_cdf(t, rates):
    if t <= 0:
        return mp.mpf(0)
    coefficients = [
        mp.fprod(rk / (rk - rj) for k, rk in enumerate(rates) if k != j)
        for j, rj in enumerate(rates)
    ]
    return 1 - mp.fsum(c * mp.exp(-r * t) for c, r in zip(coefficients, rates))


def inclusion_exclusion(mu, cap, rates):
    n = len(rates)
    terms = []
    for k in range(n + 1):
        if mu - k * cap <= 0:
            continue
        inner = mp.fsum(
            mp.exp(-cap * mp.fsum(rates[j] for j in indices))
            for indices in itertools.combinations(range(n), k)
        )
        terms.append((-1) ** k * inner * hypoexp_cdf(mu - k * cap, rates))
    numerator = mp.fsum(terms)
    denominator = hypoexp_cdf(mu, rates)
    return numerator, denominator, numerator / denominator


def inversion(mu, cap, rates):
    # Laplace transform, in the sum cutoff variable t, of
    # Pr(sum S_j <= t, every S_j <= cap). Integrals over [0, cap]
    # factor, followed by the cumulative-probability factor 1/s.
    def transform(s):
        return mp.fprod(
            r * (-mp.expm1(-(s + r) * cap)) / (s + r) for r in rates
        ) / s

    def denominator_transform(s):
        return mp.fprod(r / (s + r) for r in rates) / s

    numerator = mp.invertlaplace(transform, mu, method="dehoog")
    denominator = mp.invertlaplace(denominator_transform, mu, method="dehoog")
    return numerator, denominator, numerator / denominator


def run(dps):
    mp.mp.dps = dps
    cases = [(3, 2, 2, 5), (3, 2, 3, 5), (4, 3, 7, 20),
             (4, 3, 11, 20), (6, 4, 3, 10), (6, 4, 9, 20)]
    records = []
    for n, u_int, cap_num, cap_den in cases:
        u = mp.mpf(u_int)
        rates = [mp.mpf(j * j) / (u * u) for j in range(1, n + 1)]
        mu = mp.fsum(1 / (1 + r) for r in rates)
        cap = mu * cap_num / cap_den
        a, b, c = inclusion_exclusion(mu, cap, rates)
        ai, bi, ci = inversion(mu, cap, rates)
        error = abs(c - ci)
        # This deliberately modest tolerance allows portability of inversion
        # versions; the full numerical errors are retained below.
        assert 0 < c < 1, (n, c)
        assert error < mp.mpf("1e-20"), (n, error)
        records.append({
            "n": n, "u": str(u_int),
            "cap_over_mu": f"{cap_num}/{cap_den}",
            "mu": mp.nstr(mu, 40), "cap": mp.nstr(cap, 40),
            "conditioning_probability_hypoexp": mp.nstr(b, 40),
            "conditional_cdf_inclusion_exclusion": mp.nstr(c, 40),
            "conditional_cdf_laplace_inversion": mp.nstr(ci, 40),
            "absolute_cdf_error": mp.nstr(error, 12),
            "absolute_numerator_error": mp.nstr(abs(a - ai), 12),
            "absolute_denominator_error": mp.nstr(abs(b - bi), 12),
        })
    return {
        "method": "Finite inclusion-exclusion versus independent de Hoog Laplace inversion",
        "mpmath_version": mp.__version__, "working_decimal_precision": dps,
        "passed": len(records), "cases": records,
        "max_absolute_cdf_error": mp.nstr(max(mp.mpf(r["absolute_cdf_error"]) for r in records), 12),
        "limitations": [
            "Numerical arbitrary-precision validation, not outward-rounded interval arithmetic.",
            "Finite spectra only; does not establish the infinite-dimensional asymptotic theorem.",
            "theta=1 only; no claim of a validation for other gamma shapes.",
        ],
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--dps", type=int, default=110)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("finite_validation.json"))
    args = parser.parse_args()
    results = run(args.dps)
    args.output.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(f"Passed {results['passed']} finite cases at {args.dps} decimal digits.")
    print(f"Maximum absolute CDF discrepancy: {results['max_absolute_cdf_error']}")
    print(f"Results: {args.output}")
