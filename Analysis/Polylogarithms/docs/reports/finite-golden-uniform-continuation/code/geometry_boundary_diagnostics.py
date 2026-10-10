#!/usr/bin/env python3
"""Near-critical crossing and positive-mass diagnostics.

Uses the proved convergent local series, with analytic truncation bounds.
The arithmetic is multiprecision floating point, not outward intervals;
the results are numerical diagnostics rather than proof certificates.
Requires mpmath. Run with no arguments to regenerate the bundled JSON.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import mpmath as mp


class BoundaryKernel:
    def __init__(self, b, epsilon, terms=14):
        self.b = mp.mpf(b)
        self.p = 1 - self.b
        self.e = mp.mpf(epsilon)
        self.a = self.p + self.e
        self.terms = terms
        self.constant = self.e / (self.p * mp.gamma(1 + self.e))
        self.zeta_coefficient = mp.zeta(self.b) / mp.gamma(self.a)
        self.linear = -1 / (2 * mp.gamma(1 + self.e))
        self.even = [
            -mp.bernoulli(2 * ell) * mp.gamma(self.b + 2 * ell - 1)
            / (mp.factorial(2 * ell) * mp.gamma(self.b)
               * mp.gamma(self.e + 2 * ell))
            for ell in range(1, terms + 1)
        ]
        self.K = (mp.gamma(self.p) / (self.p * (-mp.zeta(self.b)))) ** (1 / self.p)
        self.tau = (
            mp.gamma(self.p + self.e) * self.e
            / (self.p * (-mp.zeta(self.b)) * mp.gamma(1 + self.e))
        ) ** (1 / self.p)

    def bracket(self, T):
        T = mp.mpf(T)
        if not T:
            return self.constant
        even_sum = mp.mpf(0)
        T2 = T * T
        for coefficient in reversed(self.even):
            even_sum = (even_sum + coefficient) * T2
        return (
            self.constant + self.zeta_coefficient * T ** self.p
            + self.linear * T + even_sum
        )

    def crossing(self):
        lower, upper = mp.mpf(0), self.tau
        assert self.bracket(lower) > 0
        assert self.bracket(upper) < 0
        for _ in range(240):
            mid = (lower + upper) / 2
            if self.bracket(mid) > 0:
                lower = mid
            else:
                upper = mid
        return (lower + upper) / 2

    def positive_mass_below(self, upper):
        """Integral of the local-series density e^-T k(T) on (0,upper)."""
        terms = [
            self.constant * mp.gammainc(self.e, 0, upper),
            self.zeta_coefficient * mp.gammainc(self.a, 0, upper),
            self.linear * mp.gammainc(1 + self.e, 0, upper),
        ]
        terms.extend(
            coefficient * mp.gammainc(self.e + 2 * ell, 0, upper)
            for ell, coefficient in enumerate(self.even, start=1)
        )
        return mp.fsum(terms)

    def bracket_tail_bound(self, T):
        # |B_(2ell)|/(2ell)! <= 4/(2pi)^(2ell), and the gamma
        # ratio in the series coefficient is <= 1 for these parameters.
        ratio = T / (2 * mp.pi)
        return 4 * ratio ** (2 * self.terms + 2) / (1 - ratio ** 2)

    def mass_tail_bound(self, T):
        ratio = T / (2 * mp.pi)
        exponent = self.e + 2 * self.terms + 2
        return (
            4 * T ** self.e * ratio ** (2 * self.terms + 2)
            / (exponent * (1 - ratio ** 2))
        )


def text(x):
    return mp.nstr(x, 38)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--output", type=Path,
        default=Path(__file__).resolve().parents[1] / "data/geometry_boundary_diagnostics.json",
    )
    args = parser.parse_args()
    mp.mp.dps = 90
    rows = []
    epsilons = ["0.02", "0.01", "0.005", "0.002", "0.001", "0.0005", "0.0001"]
    for b in ["0.25", "0.5", "0.75"]:
        for e in epsilons:
            kernel = BoundaryKernel(b, e)
            T = kernel.crossing()
            leading = kernel.K * kernel.e ** (1 / kernel.p)
            corrected = kernel.tau - kernel.tau ** 2 / (2 * kernel.e)
            M = kernel.positive_mass_below(T)
            assert M > 0
            assert T < mp.mpf("0.1")
            y_cutoff = -kernel.e * mp.log(T)
            distributions = []
            for ystr in ["0.25", "0.5", "1", "2"]:
                y = mp.mpf(ystr)
                cutoff = mp.exp(-y / kernel.e)
                cdf = (
                    mp.mpf(0) if cutoff >= T
                    else 1 - kernel.positive_mass_below(cutoff) / M
                )
                target = 1 - mp.exp(-y)
                assert 0 <= cdf <= 1
                distributions.append({
                    "y": ystr, "positive_mass_cdf": text(cdf),
                    "exponential_cdf": text(target), "absolute_error": text(abs(cdf-target)),
                })
            row = {
                "b": b, "epsilon": e, "p": text(kernel.p), "a": text(kernel.a),
                "T_crossing": text(T), "K_b": text(kernel.K),
                "leading_crossing": text(leading), "tau": text(kernel.tau),
                "two_term_crossing": text(corrected),
                "T_over_leading": text(T / leading),
                "first_correction_ratio": text((kernel.tau - T) / (kernel.tau ** 2 / (2 * kernel.e))),
                "scaled_two_term_remainder": text((T - corrected) / (kernel.tau ** 3 / kernel.e ** 2)),
                "p_times_positive_mass": text(kernel.p * M),
                "Y_support_lower_endpoint": text(y_cutoff),
                "series_bracket_tail_bound": text(kernel.bracket_tail_bound(T)),
                "series_mass_tail_bound": text(kernel.mass_tail_bound(T)),
                "Y_distribution": distributions,
            }
            if b == "0.5":
                expected_coefficient = -4 * mp.log(2) - 2 * mp.pi / mp.zeta(mp.mpf("0.5")) ** 2
                row["symmetric_relative_correction_over_epsilon"] = text((T / leading - 1) / kernel.e)
                row["symmetric_expected_coefficient"] = text(expected_coefficient)
            rows.append(row)

    for b in ["0.25", "0.5", "0.75"]:
        branch = [row for row in rows if row["b"] == b]
        assert abs(mp.mpf(branch[-1]["T_over_leading"]) - 1) < abs(mp.mpf(branch[0]["T_over_leading"]) - 1)
        assert abs(mp.mpf(branch[-1]["first_correction_ratio"]) - 1) < abs(mp.mpf(branch[0]["first_correction_ratio"]) - 1)
        assert abs(mp.mpf(branch[-1]["p_times_positive_mass"]) - 1) < abs(mp.mpf(branch[0]["p_times_positive_mass"]) - 1)

    result = {
        "status": "all diagnostic assertions passed",
        "precision_decimal_digits": mp.mp.dps,
        "bernoulli_even_terms": 14,
        "rounding_status": "Multiprecision floating point; analytic series-tail bounds exclude rounding and are not interval certificates.",
        "theorems": "article/real_boundary.tex",
        "rows": rows,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({
        "output": str(args.output), "rows": len(rows),
        "cdf_comparisons": sum(len(row["Y_distribution"]) for row in rows),
        "status": result["status"],
    }, indent=2))


if __name__ == "__main__":
    main()
