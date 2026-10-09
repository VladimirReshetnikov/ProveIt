#!/usr/bin/env python3
"""Independent numerical checks of the correction section.

The mathematical proofs are in sections/corrections_gamma.tex. These checks
compare integrals or finite sums with the corrected identities; they are
regression checks and are not interval-arithmetic proof certificates.
Requires mpmath. Run from any directory; --output selects the JSON destination.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import mpmath as mp


def clausen2(theta):
    return mp.im(mp.polylog(2, mp.exp(mp.j * theta)))


def character_l5(s):
    return sum(c * mp.zeta(s, mp.mpf(r) / 5)
               for r, c in [(1, 1), (2, -1), (3, -1), (4, 1)]) / mp.power(5, s)


def sine_log_square_sum(q):
    return sum(mp.log(2 * mp.sin(mp.pi * r / q)) ** 2
               for r in range(1, q))


def herglotz_difference(p, q):
    """Radchenko-Zagier finite sum for F(p/q)-F(1)."""
    roots_p = [mp.exp(2 * mp.pi * mp.j * r / p) for r in range(p)]
    roots_q = [mp.exp(2 * mp.pi * mp.j * r / q) for r in range(q)]

    def summand(alpha, beta):
        return (mp.polylog(2, beta / (beta - 1))
                - mp.polylog(2, (alpha - beta) / (1 - beta)))

    return sum(sum(summand(alpha, beta) for beta in roots_q[1:])
               - sum(summand(alpha, beta) for beta in roots_p[1:])
               for alpha in roots_p)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dps", type=int, default=70)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1]
                        / "data" / "corrections_checks.json")
    args = parser.parse_args()
    mp.mp.dps = args.dps
    tolerance = mp.power(10, -args.dps + 15)
    checks = []

    def record(name, lhs, rhs):
        error = abs(lhs - rhs)
        passed = bool(error < tolerance)
        checks.append({"name": name, "lhs_real": mp.nstr(mp.re(lhs), args.dps),
                       "rhs_real": mp.nstr(mp.re(rhs), args.dps),
                       "absolute_error": mp.nstr(error, 10), "passed": passed})
        if not passed:
            raise AssertionError(f"{name}: error {mp.nstr(error, 15)}")

    zeta_prime_minus_one = mp.diff(mp.zeta, -1)
    for numerator, denominator in [(1, 5), (2, 7)]:
        a = mp.mpf(numerator) / denominator
        lhs = mp.quad(mp.loggamma, [0, a])
        rhs = (mp.diff(lambda s: mp.zeta(s, a), -1) - zeta_prime_minus_one
               + (a - a*a)/2 + a * mp.log(2*mp.pi)/2)
        record(f"loggamma_general_{numerator}_{denominator}", lhs, rhs)

    integral_fifth = mp.quad(mp.loggamma, [0, mp.mpf(1)/5])
    fifth_rhs = (mp.mpf(2)/25 + mp.log(2*mp.pi)/10
                 + clausen2(2*mp.pi/5)/(4*mp.pi)
                 - mp.mpf(6)/5*zeta_prime_minus_one
                 + mp.diff(character_l5, -1)/20
                 - mp.mpf(29)/1200*mp.log(5))
    record("loggamma_fifth_character_correction", integral_fifth, fifth_rhs)
    record("quadratic_L5_minus_one", character_l5(-1), -mp.mpf(2)/5)

    seventh_rhs = (-mp.mpf(19)/28*mp.pi**2
                   - sine_log_square_sum(7)/2)
    record("herglotz_one_seventh", herglotz_difference(1, 7), seventh_rhs)
    six_sevenths_rhs = (-mp.mpf(8)/63*mp.pi**2 + mp.polylog(2, mp.mpf(6)/7)
                        + mp.log(mp.mpf(7)/6)**2/2
                        - sine_log_square_sum(7)/2 + sine_log_square_sum(6)/2)
    record("herglotz_six_sevenths", herglotz_difference(6, 7), six_sevenths_rhs)

    j_half = mp.quad(lambda t: mp.log(1+mp.sqrt(t))/(1+t), [0, 1])
    record("J_half_counterexample", j_half, mp.pi**2/48 + mp.log(2)**2/4)

    for q in [4, 6, 8]:
        x = mp.mpf(2)/q
        fp = mp.nsum(lambda n: mp.polygamma(1, n*x)-1/(n*x), [1, mp.inf])
        w_star = sum(mp.cot(2*mp.pi*r/q) * clausen2(2*mp.pi*r/q)
                     for r in range(1, q) if 2*r != q)
        rhs = (1 + mp.log(2) + mp.mpf(q*q-4)/(24*q)*mp.pi**2
               + w_star - mp.log(2))
        record(f"herglotz_derivative_even_q_{q}", x*fp, rhs)
        if q == 4:
            record("herglotz_derivative_half_elementary", fp, 2+mp.pi**2/4)

    report = {"precision_decimal_digits": args.dps,
              "tolerance": mp.nstr(tolerance, 10),
              "interpretation": "Numerical regression evidence; proofs are in the article.",
              "all_passed": all(c["passed"] for c in checks),
              "check_count": len(checks), "checks": checks}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"{len(checks)} checks passed at {args.dps} decimal digits; {args.output}")


if __name__ == "__main__":
    main()
