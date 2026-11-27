#!/usr/bin/env python3
"""Exploratory quadrature check for the xi small-deviation asymptotic.

This is floating-point evidence, not an interval certificate.  The proof
is in xi_small_deviations.tex.  The quadrature truncates a standardized
Fourier integral at 20; the default parameters lie deeply in the Gaussian
tilt regime.  mpmath is the only dependency.
"""

import json
from pathlib import Path
import mpmath as mp


def log_xi(s):
    return (mp.log(mp.mpf("0.5")) + mp.log(s) + mp.log(s - 1)
            - (s / 2) * mp.log(mp.pi) + mp.loggamma(s / 2)
            + mp.log(mp.zeta(s)))


def xi_center():
    s = mp.mpf("0.5")
    return s * (s - 1) / 2 * mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s)


def one_row(u_value):
    u = mp.mpf(u_value)
    t = u*u
    hp = mp.diff(lambda z: log_xi(z + mp.mpf("0.5")), u)
    hpp = mp.diff(lambda z: log_xi(z + mp.mpf("0.5")), u, 2)
    x = hp/(2*u)
    variance = hp/(4*u**3) - hpp/(4*u**2)
    sigma = mp.sqrt(variance)
    a = t*sigma
    log_base = log_xi(u + mp.mpf("0.5"))
    c0 = xi_center()
    K = log_base - mp.log(c0)

    def phi(w):
        s = mp.mpf("0.5") + mp.sqrt(t - 1j*w/sigma)
        return mp.exp(log_base - log_xi(s) - 1j*w*x/sigma)

    grid = [0, 1, 2, 4, 8, 12, 16, 20]
    p_zero = mp.quad(lambda w: mp.re(phi(w)), grid)/mp.pi
    cdf_tilt_factor = mp.quad(
        lambda w: mp.re(phi(w)/(1 - 1j*w/a)), grid)/(mp.pi*a)

    v = -mp.lambertw(-8*mp.pi*x, -1).real
    u_leading = v/(4*x)
    log_A = (mp.log(2**mp.mpf("1.25") * c0 / mp.pi**mp.mpf("0.75"))
             - mp.mpf("2.25")*mp.log(u_leading)
             - mp.log(v - 1)/2 - u_leading*(v - 2)/4)
    log_F = t*x - K + mp.log(cdf_tilt_factor)
    log_f = t*x - K + mp.log(p_zero/sigma)
    ratio_F = mp.exp(log_F - log_A)
    ratio_f = mp.exp(log_f - log_A - 2*mp.log(u_leading))

    ell = mp.log(u/(2*mp.pi))
    xi_main = (u*(ell-1)/2 + mp.mpf("1.75")*mp.log(u)
               + mp.log(mp.pi/2)/4)
    stirling_scaled = u*(log_base - xi_main)
    return {
        "true_saddle_u": str(u_value),
        "x": mp.nstr(x, 20),
        "leading_saddle_u": mp.nstr(u_leading, 20),
        "cdf_ratio_to_A": mp.nstr(ratio_F, 20),
        "density_ratio_to_u_squared_A": mp.nstr(ratio_f, 20),
        "predicted_first_relative_correction": mp.nstr(1/(48*u_leading), 20),
        "log_cdf": mp.nstr(log_F, 24),
        "scaled_log_xi_remainder_tends_to_minus_1_over_48": mp.nstr(stirling_scaled, 20),
    }


def main():
    mp.mp.dps = 60
    rows = [one_row(v) for v in (100, 1000, 10000)]
    output = {
        "status": "exploratory floating-point quadrature, not certified",
        "mpmath_version": mp.__version__,
        "decimal_precision": mp.mp.dps,
        "standardized_fourier_cutoff": 20,
        "rows": rows,
    }
    path = Path(__file__).resolve().parents[1] / "checks" / "xi_small_deviations_checks.json"
    path.parent.mkdir(exist_ok=True)
    path.write_text(json.dumps(output, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
