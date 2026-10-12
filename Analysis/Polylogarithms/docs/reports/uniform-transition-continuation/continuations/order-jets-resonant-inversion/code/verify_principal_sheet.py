#!/usr/bin/env python3
"""Independent numerical branch check for a principal-sheet polylogarithm zero.

The root is located by a finite truncation of the convergent local expansion.
It is then evaluated by the defining Bose integral after v=log(u), which is
independent of that expansion. mpmath quadrature is not directed interval
arithmetic; the reported residual is a diagnostic, not a proof certificate.
The article's analytic implicit-function proof establishes existence.
"""

import argparse
import json
from pathlib import Path

import mpmath as mp


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("principal_sheet_check.json"))
    args = parser.parse_args()
    mp.mp.dps = 90
    beta = mp.mpf("0.2")
    epsilon = 1j * beta
    s = 1 + epsilon
    gamma = mp.gamma(1 - epsilon)
    Z = epsilon * mp.zeta(s)
    tau = mp.exp(-2 * mp.pi / beta)

    def local_tail(t):
        return mp.fsum(mp.zeta(s - j) * (-t)**j / mp.factorial(j)
                       for j in range(1, 12))

    a0 = mp.exp((mp.log(Z) - mp.log(gamma)) / epsilon)
    a = mp.findroot(
        lambda u: (gamma * mp.exp(epsilon * mp.log(u)) - Z) / epsilon
                  - local_tail(tau * u),
        (a0, a0 * mp.mpf("1.001")))
    t = tau * a

    # Li_s(e^-t) = 1/Gamma(s) int_R exp(s v)/(exp(exp(v)+t)-1) dv
    # for Re(s)>0 and Re(t)>0. Real v fixes u^(s-1) unambiguously.
    intervals = [-300, -100, -50, -35, -30, -20, -10, 0, 4, 8]
    integrand = lambda v: mp.exp(s * v) / mp.expm1(mp.exp(v) + t)
    integral = mp.quad(integrand, intervals) / mp.gamma(s)

    # These analytic truncation bounds do not estimate quadrature roundoff.
    # |exp(u+t)-1| >= exp(u+Re(t))-1 >= Re(t), with u>0.
    left_bound = mp.exp(intervals[0]) / (mp.re(t) * abs(mp.gamma(s)))
    # For the right tail, substitute u=exp(v) and integrate 1/(exp(u)-1).
    e8 = mp.exp(intervals[-1])
    right_log10_bound = (-e8 - mp.log1p(-mp.exp(-e8))
                         - mp.log(abs(mp.gamma(s)))) / mp.log(10)

    def decimal(value):
        return mp.nstr(value, 65)

    report = {
        "status": "passed",
        "provenance": "Numerical diagnostic; no directed rounding or interval quadrature.",
        "mpmath_version": mp.__version__,
        "decimal_precision": mp.mp.dps,
        "beta": decimal(beta),
        "k": 1,
        "local_tail_terms": 11,
        "root": {"real_t": decimal(mp.re(t)), "imag_t": decimal(mp.im(t)),
                 "principal_slit": bool(abs(mp.arg(t)) < mp.pi),
                 "Re_t_positive": bool(mp.re(t) > 0),
                 "modulus_z": decimal(abs(mp.exp(-t)))},
        "independent_reference": "Bose integral, with v=log(u) and real v",
        "quadrature_intervals": intervals,
        "integral_residual": decimal(abs(integral)),
        "analytic_left_tail_bound": decimal(left_bound),
        "analytic_right_tail_bound_log10": decimal(right_log10_bound),
        "mpmath_polylog_residual": decimal(abs(mp.polylog(s, mp.exp(-t)))),
    }
    assert report["root"]["Re_t_positive"]
    assert abs(integral) < mp.mpf("1e-75")
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
