#!/usr/bin/env python3
"""Independent finite-binomial-sum check for B(z)=(z+z^2)/2, rho=1."""
import sys
sys.dont_write_bytecode = True
import math
import numpy as np
import scipy
from scipy.special import gammaln
from _common import BOUNDARY, emit_json, parser, require


def run(nmax=20000):
    require(100 <= nmax <= 20000, "max-n must be in [100, 20000]")
    sigma = np.zeros(nmax + 1)
    for d in range(1, nmax + 1, 2):
        sigma[d::d] += d
    c = np.zeros(nmax + 1)
    c[1:] = sigma[1:] / np.arange(1, nmax + 1)
    mu, variance, kappa3 = 1.5, .25, 0.
    damping = variance / (2 * mu**2)
    q = kappa3 / (6 * mu**2) - variance**2 / (4 * mu**3)
    constant = math.pi**2 / (12 * mu)
    rows = []
    samples = sorted({n for n in (100, 300, 1000, 3000, 10000, 20000, nmax) if n <= nmax})
    for n in samples:
        k = np.arange((n + 1) // 2, n + 1)
        logweights = gammaln(k + 1) - gammaln(n - k + 1) - gammaln(2*k - n + 1) - k*np.log(2.)
        coeff = float(np.sum(c[k] * np.exp(logweights)))
        h0, h1 = 0., 0.
        for m in range(1, 100):
            a = 2 * math.pi**2 * m
            weight = c[m] * math.exp(-a*damping) * (a/mu)**.25 / math.sqrt(math.pi)
            phase = 2 * math.sqrt(a*n/mu) + math.pi/4
            correction = q*a**1.5/math.sqrt(mu) + 3*math.sqrt(mu)/(16*math.sqrt(a))
            h0 -= weight * math.cos(phase)
            h1 += weight * correction * math.sin(phase)
        first_scaled = n**1.25 * (coeff - constant - n**(-.75)*h0)
        second_scaled = n**1.75 * (coeff - constant - n**(-.75)*h0 - n**(-1.25)*h1)
        require(all(math.isfinite(v) for v in (coeff, h0, h1, first_scaled, second_scaled)), "nonfinite two-point result")
        require(abs(second_scaled) < 1, f"two-point finite residual regression n={n}")
        rows.append({"n": n, "coefficient": coeff, "H0": h0, "H1": h1,
                     "after_H0_times_n_5_over_4": first_scaled,
                     "after_H0_H1_times_n_7_over_4": second_scaled})
    return {"schema_version": 1, "status": "PASS", "diagnostic": "two_point_decoration",
            "max_n": nmax, "eta_modes": 99, "arithmetic": "IEEE 754 binary64",
            "decoration": "(z+z^2)/2", "rho": 1, "mu": mu, "variance": variance,
            "kappa3": kappa3, "d": damping, "q": q, "C": constant,
            "coefficient_method": "finite binomial sum, evaluated via log-gamma",
            "rows": rows, "checks": {"absolute_n_7_over_4_residual_limit_exclusive": 1},
            "versions": {"numpy": np.__version__, "scipy": scipy.__version__}, "boundary": BOUNDARY}


def main():
    p = parser(__doc__)
    p.add_argument("--max-n", type=int, default=20000)
    args = p.parse_args()
    emit_json(run(args.max_n), args.output)


if __name__ == "__main__":
    main()
