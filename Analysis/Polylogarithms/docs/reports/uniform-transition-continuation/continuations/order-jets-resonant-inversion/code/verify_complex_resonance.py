#!/usr/bin/env python3
"""High-precision diagnostics for the complex resonance theorems.

The proofs do not depend on this script. These are ordinary mpmath checks,
not outward-rounded certificates. Requires mpmath.
Run: python verify_complex_resonance.py --output complex_resonance_checks.json
"""

import argparse
import json
from pathlib import Path

import mpmath as mp


def show(z, digits=45):
    z = mp.mpc(z)
    return {"real": mp.nstr(z.real, digits), "imag": mp.nstr(z.imag, digits)}


def tail_pair(eps, t):
    """Evaluate A and E from the normally convergent Jonquiere tails."""
    a = mp.mpc(0)
    e = mp.mpc(0)
    term_power = mp.mpc(1)
    for j in range(1, 60):
        term_power *= -t / j
        term = mp.zeta(1 + eps - j) * term_power
        a += term
        e += term / (j + 1)
        # Four initial terms avoid premature termination near a zeta zero.
        if j >= 4 and abs(term) < mp.eps * max(abs(a), mp.mpf("1e-100")):
            return a, e
    raise RuntimeError("Tail did not converge within the diagnostic cap")


def regular_zeta(eps):
    return mp.zeta(1 + eps) - 1 / eps


def critical_equation(eps, tau, u):
    a, _ = tail_pair(eps, tau * u)
    return -mp.expm1(mp.loggamma(1 - eps) + eps * mp.log(u)) / eps \
        + regular_zeta(eps) + a


def paired_phi(eps, delta_lambda, y, u):
    _, e = tail_pair(eps, y * u)
    log_r = mp.loggamma(1 - eps) - mp.log1p(eps)
    q = -mp.expm1(log_r - delta_lambda + eps * mp.log(u)) / eps \
        + regular_zeta(eps) + e
    return u * q - 1


def paired_phi_prime(eps, delta_lambda, y, u):
    a, _ = tail_pair(eps, y * u)
    return -mp.expm1(mp.loggamma(1 - eps) - delta_lambda
                     + eps * mp.log(u)) / eps + regular_zeta(eps) + a


def critical_checks():
    rows = []
    for beta_string in ("0.1", "0.2", "-0.15"):
        beta = mp.mpf(beta_string)
        eps = 1j * beta
        z1 = eps * mp.zeta(1 + eps)
        a0 = mp.exp((mp.log(z1) - mp.loggamma(1 - eps)) / eps)
        b0 = a0 * z1 / (1 + eps)
        a_tau = -mp.zeta(eps) * a0 ** 2 / z1
        b_tau = -mp.zeta(eps) * a0 ** 2 / 2
        previous = None
        for index in (1, 2, 3):
            k = index if beta > 0 else -index
            tau = mp.exp(-2 * mp.pi * k / beta)
            guess = a0 + a_tau * tau
            u = mp.findroot(lambda v: critical_equation(eps, tau, v),
                            (guess, guess * (1 + mp.mpf("1e-12"))),
                            tol=mp.mpf("1e-150"), maxsteps=30)
            tc = tau * u
            at, et = tail_pair(eps, tc)
            yc = tc * (z1 / (1 + eps) + et - at / (1 + eps))
            direct_critical = mp.polylog(1 + eps, mp.exp(-tc))
            direct_value = mp.zeta(2 + eps) - mp.polylog(2 + eps, mp.exp(-tc))
            # A simple critical point has F'' = -Li_epsilon(exp(-t)).
            direct_second_scaled = -tc * mp.polylog(eps, mp.exp(-tc))
            row = {
                "beta": beta_string, "k": k, "tau": mp.nstr(tau, 45),
                "t_over_tau": show(u), "y_over_tau": show(yc / tau),
                "paired_critical_residual": mp.nstr(abs(critical_equation(eps, tau, u)), 12),
                "direct_critical_residual": mp.nstr(abs(direct_critical), 12),
                "direct_critical_value_relative_error": mp.nstr(abs((direct_value-yc)/yc), 12),
                "a_tau_coefficient_error": mp.nstr(abs((u-a0)/tau-a_tau), 12),
                "b_tau_coefficient_error": mp.nstr(abs((yc/tau-b0)/tau-b_tau), 12),
                "scaled_second_derivative": show(direct_second_scaled),
                "second_derivative_leading_error": mp.nstr(abs(direct_second_scaled+z1), 12),
            }
            if previous is not None:
                ratio = mp.exp(-2 * mp.pi / abs(beta))
                row["critical_point_ratio_relative_error"] = mp.nstr(abs(tc/previous[0]/ratio-1), 12)
                row["critical_value_ratio_relative_error"] = mp.nstr(abs(yc/previous[1]/ratio-1), 12)
            rows.append(row)
            previous = (tc, yc)
    return rows


def splitting_checks(D, r1):
    rows = []
    for k in (1, -1, 2):
        lam0 = 2j * mp.pi * k
        for Yint in (80, 160, 320):
            Y = mp.mpf(Yint)
            y = mp.exp(-Y)
            eps = lam0 / Y
            rho = 1 / mp.sqrt(Y)
            c0 = mp.sqrt(-2 * lam0 * D)
            d = -lam0 * (r1 + 4 * D / 3)
            roots = []
            for sign in (1, -1):
                c = sign * c0
                u_first = 1 + c * rho
                u_second = u_first + d / Y
                u = mp.findroot(lambda v: paired_phi(eps, 0, y, v), u_second,
                                df=lambda v: paired_phi_prime(eps, 0, y, v),
                                solver="newton", tol=mp.mpf("1e-150"), maxsteps=40)
                tc = y * u
                direct = (mp.zeta(2 + eps)-mp.polylog(2 + eps, mp.exp(-tc))) / y - 1
                rows.append({
                    "k": k, "Y": Yint, "branch": sign, "t_over_y": show(u),
                    "first_order_error": mp.nstr(abs(u-u_first), 14),
                    "second_order_error": mp.nstr(abs(u-u_second), 14),
                    "second_error_times_Y_to_3_over_2": mp.nstr(abs(u-u_second)*Y**mp.mpf("1.5"), 14),
                    "paired_residual": mp.nstr(abs(paired_phi(eps, 0, y, u)), 12),
                    "direct_relative_residual": mp.nstr(abs(direct), 12),
                    "inverse_derivative": show(paired_phi_prime(eps, 0, y, u)),
                })
                roots.append(u)
            assert abs(roots[0]-roots[1]) > rho
    return rows


def unfolding_checks(D, r1):
    rows = []
    lam0 = 2j * mp.pi
    eta_star = lam0**2 * D
    for fraction in (mp.mpf("0"), mp.mpf("0.5"), mp.mpf("1.5")):
        eta = fraction * eta_star
        for Yint in (160, 320):
            Y = mp.mpf(Yint)
            y = mp.exp(-Y)
            delta = eta / Y**2
            eps = (lam0 + delta) / Y
            c0 = mp.sqrt(2*eta/lam0-2*lam0*D)
            d = 4*eta/(3*lam0)-lam0*(r1+4*D/3)
            for sign in (1, -1):
                approximation = 1+sign*c0/mp.sqrt(Y)+d/Y
                u = mp.findroot(lambda v: paired_phi(eps, delta, y, v), approximation,
                                df=lambda v: paired_phi_prime(eps, delta, y, v),
                                solver="newton", tol=mp.mpf("1e-150"), maxsteps=40)
                rows.append({
                    "eta_over_eta_star": str(fraction), "Y": Yint, "branch": sign,
                    "t_over_y": show(u),
                    "second_order_error": mp.nstr(abs(u-approximation), 14),
                    "second_error_times_Y_to_3_over_2": mp.nstr(abs(u-approximation)*Y**mp.mpf("1.5"), 14),
                    "paired_residual": mp.nstr(abs(paired_phi(eps, delta, y, u)), 12),
                })
    return rows


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", default="complex_resonance_checks.json")
    args = parser.parse_args()
    mp.mp.dps = 220
    r1 = mp.euler-1
    r2 = (r1**2+mp.zeta(2)+1)/2
    D = r2+mp.stieltjes(1)
    C = D+r1
    data = {
        "precision_decimal_digits": mp.mp.dps,
        "status": "High-precision diagnostics, not rigorous interval certificates",
        "constants": {"C": mp.nstr(C, 80), "D": mp.nstr(D, 80),
                      "gamma1": mp.nstr(mp.stieltjes(1), 80)},
        "critical_lattice": critical_checks(),
        "branch_splitting": splitting_checks(D, r1),
        "parameter_unfolding": unfolding_checks(D, r1),
    }
    Path(args.output).write_text(json.dumps(data, indent=2)+"\n")
    print(json.dumps({"output": str(Path(args.output).resolve()),
                      "critical_checks": len(data["critical_lattice"]),
                      "splitting_checks": len(data["branch_splitting"]),
                      "unfolding_checks": len(data["parameter_unfolding"]),
                      "C": mp.nstr(C, 20), "D": mp.nstr(D, 20)}, indent=2))


if __name__ == "__main__":
    main()
