#!/usr/bin/env python3
"""Independent numerical reproduction of the classical cubic log-gamma formula.

Only mpmath is required.  Analytic series-truncation bounds are reported; the
floating-point evaluations are NOT interval-certified.  See cubic_notes.tex for
the proof and the distinction between numerical checks and rigorous identities.

The split at t=1 uses the polylogarithm expansion at t=0 and exponentially
convergent sums at infinity. This is the same general acceleration principle as
Bailey--Borwein--Borwein (2015), implemented independently here.
"""

import argparse
import json
from pathlib import Path

import mpmath as mp


def tornheim_partials(dps=100, degree=150, diagonal=300):
    mp.mp.dps = dps
    gamma = mp.euler
    ell = mp.log(2 * mp.pi)
    alpha = mp.stieltjes(1) + gamma**2 / 2 + mp.pi**2 / 12
    b = [mp.mpf(0)] * (degree + 1)
    c = [mp.mpf(0)] * (degree + 1)
    for k in range(1, degree + 1):
        # Exact functional equations avoid huge negative-order zeta derivatives.
        if k == 1:
            c[k] = mp.mpf(1) / 2
            b[k] = ell / 2
        elif k % 2 == 0:
            c[k] = (-1) ** (k // 2) * 2 * mp.zeta(k) / (k * (2 * mp.pi) ** k)
            zeta_log_derivative = mp.diff(mp.zeta, k) / mp.zeta(k)
            b[k] = c[k] * (ell - mp.digamma(k) - zeta_log_derivative)
        else:
            b[k] = ((-1) ** ((k + 1) // 2) * mp.pi * mp.zeta(k)
                    / (k * (2 * mp.pi) ** k))

    # Integral from 0 to 1.  Every logarithmic integral is evaluated exactly
    # as int_0^1 t^k log(t)^j dt = (-1)^j j!/(k+1)^(j+1).
    tab = alpha**2 - 2 * alpha * gamma + 2 * alpha + 2 * gamma**2 - 6 * gamma + 6
    tac = -alpha * gamma + 2 * alpha + 2 * gamma**2 - 9 * gamma + 12
    tc = -6 + 2 * gamma
    for k in range(1, degree + 1):
        d = mp.mpf(k + 1)
        tab += 2 * b[k] * (-alpha / d + gamma / d**2 - 1 / d**3)
        tac += b[k] * (-2 / d**3 + gamma / d**2)
        tac += c[k] * (-alpha * gamma / d + (alpha + gamma**2) / d**2
                        - 3 * gamma / d**3 + 3 / d**4)
        tc += -2 * c[k] * (2 / d**3 - gamma / d**2)
        for j in range(1, degree + 1):
            e = mp.mpf(k + j + 1)
            tab += b[k] * b[j] / e
            tac += b[k] * c[j] * (gamma / e - 1 / e**2)
            tc += c[k] * c[j] * (gamma / e - 1 / e**2)

    # Integral from 1 to infinity, grouped by k=m+n.
    logs = [mp.mpf(0)] + [mp.log(k) for k in range(1, diagonal)]
    for k in range(2, diagonal + 1):
        conv00 = mp.fsum(mp.mpf(1) / (m * (k - m)) for m in range(1, k))
        conv10 = mp.fsum(logs[m] / (m * (k - m)) for m in range(1, k))
        conv11 = mp.fsum(logs[m] * logs[k - m] / (m * (k - m)) for m in range(1, k))
        expk = mp.exp(-k)
        weight = (gamma * expk + mp.e1(k)) / k
        tab += conv11 * expk / k
        tac -= conv10 * weight
        tc += conv00 * weight

    eps_b = mp.mpf(12) / 5 * mp.mpf(6) ** (-degree)
    eps_c = mp.mpf(2) / 5 * mp.mpf(6) ** (-degree)
    q = mp.exp(-1)
    tail = 4 * q ** (diagonal + 1) * ((diagonal + 1) - diagonal * q) / (1 - q)**2
    analytic_errors = {
        "T_ab": eps_b * (12 + eps_b) + tail,
        "T_ac": 5 * eps_b + 15 * eps_c + 2 * eps_b * eps_c + tail,
        "T_c": 10 * eps_c + 2 * eps_c**2 + tail,
    }
    return tc, tab, tac, analytic_errors


def check(dps=100, degree=150, diagonal=300):
    tc, tab, tac, errors = tornheim_partials(dps, degree, diagonal)
    a = mp.log(2 * mp.pi) / 2
    A = mp.euler + 2 * a
    zeta_prime = mp.diff(mp.zeta, 2)
    zeta_second = mp.diff(mp.zeta, 2, 2)
    variance = mp.pi**2 / 48 + A**2 / 12 - A * zeta_prime / mp.pi**2 + zeta_second / (2 * mp.pi**2)
    formula = (a**3 + 3 * a * variance + 3 * mp.zeta(3) / 16
               + 3 / (8 * mp.pi**2) * (2 * A**2 * mp.zeta(3) - 2 * A * tc + 2 * tac - tab))
    # Well-conditioned quadrature after x=exp(-u), over a sufficiently long
    # finite interval; the exact omitted integral is negligible at this dps.
    # mpmath loggamma(exp(-u)) is finite even at large u.
    cutoff = (dps + 30) * mp.log(10)
    direct = mp.quad(lambda u: mp.exp(-u) * mp.loggamma(mp.exp(-u))**3,
                     [0, 1, 4, 16, 64, cutoff])
    tc_direct = mp.quad(lambda t: mp.log(-mp.expm1(-t))**2 * (mp.log(t) + mp.euler),
                        [0, mp.mpf('0.1'), 1, 4, 16, 64, cutoff])
    ta = tc / 2 + mp.diff(mp.zeta, 3)
    s_gamma = 2 * mp.euler**2 * mp.zeta(3) - 2 * mp.euler * ta + tab
    stringify = lambda x: mp.nstr(x, dps)
    out = {
        "parameters": {"dps": dps, "degree": degree, "diagonal": diagonal},
        "T_c_111": stringify(tc),
        "T_ab_111": stringify(tab),
        "T_ac_111": stringify(tac),
        "T_a_111": stringify(ta),
        "M3_formula": stringify(formula),
        "M3_quadrature": stringify(direct),
        "M3_difference": stringify(formula - direct),
        "T_c_quadrature_difference": stringify(tc - tc_direct),
        "S_gamma": stringify(s_gamma),
        "analytic_truncation_bounds_only": {k: stringify(v) for k, v in errors.items()},
        "qualification": "Analytic truncation is rigorously bounded; mpmath rounding and quadrature are not ball-certified.",
    }
    return out


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--dps", type=int, default=100)
    parser.add_argument("--degree", type=int, default=150)
    parser.add_argument("--diagonal", type=int, default=300)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = check(args.dps, args.degree, args.diagonal)
    rendered = json.dumps(result, indent=2)
    if args.output:
        args.output.write_text(rendered + "\n")
    print(rendered)
