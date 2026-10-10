#!/usr/bin/env python3
"""Diagnostics for the subunit signed-kernel theorem.

The written proofs establish all-parameter claims. These floating-point
checks verify normalizations and asymptotic coefficients, not inequalities
or certified root intervals. Requires only mpmath. Default output is JSON
beside this script; use --output PATH to change it.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import mpmath as mp


def q(t):
    if t == 0:
        return mp.mpf("0.5")
    if abs(t) < mp.mpf("0.01"):
        return mp.mpf("0.5") + mp.fsum(
            mp.bernoulli(2*k) * t**(2*k-1) / mp.factorial(2*k)
            for k in range(1, 16)
        )
    return -1 / mp.expm1(-t) - 1/t


def normalized_q_beta(a, b, T):
    """Integral beta(a,b)*q(Tv)/(Gamma(a)Gamma(b)), for |T|<1.

    Evaluate the convergent Bernoulli expansion and beta moments, with
    enough terms for the fixed diagnostic precision. No numerical endpoint
    quadrature is required even when a is small.
    """
    assert abs(T) < 1
    terms = [mp.mpf("0.5")]
    for k in range(1, 46):
        j = 2*k-1
        terms.append(mp.bernoulli(2*k) * T**j / mp.factorial(2*k)
                     * mp.rf(b, j) / mp.rf(a+b, j))
    return mp.fsum(terms) / mp.gamma(a+b)


def crossing_equation(a, b, T):
    C = normalized_q_beta(a, b, T)
    if b < 1:
        return (1/((1-b)*mp.gamma(a+b-1))
                + mp.zeta(b)*T**(1-b)/mp.gamma(a) - T*C)
    if b > 1:
        return (mp.zeta(b)/mp.gamma(a)
                - T**(b-1)/((b-1)*mp.gamma(a+b-1)) - T**b*C)
    return ((mp.euler+mp.digamma(a)-mp.log(T))/mp.gamma(a) - T*C)


def bisect_crossing(a, b, upper):
    # The upper balancing point is proved to lie above the actual root.
    low = upper / 2
    while crossing_equation(a, b, low) < 0:
        low /= 2
    high = upper
    for _ in range(180):
        mid = (low+high)/2
        if crossing_equation(a, b, mid) > 0:
            low = mid
        else:
            high = mid
    return (low+high)/2


def moment_checks():
    rows = []
    for a_s, b_s in [("0.4", "0.8"), ("0.1", "0.9"),
                     ("0.4", "1"), ("0.4", "1.4"),
                     ("1.7", "0.2"), ("0", "2.3")]:
        a, b = mp.mpf(a_s), mp.mpf(b_s)
        for n in [1, 2, 3, 7]:
            nmp = mp.mpf(n)
            if b == 1:
                q_laplace = mp.quad(lambda t: mp.exp(-nmp*t)*q(t),
                                    [0, 1, mp.inf])
                got = nmp**(-a)*(mp.euler+mp.log(nmp)-q_laplace)
            else:
                # Subtract q(0)=1/2 analytically to remove the weakest
                # endpoint singularity and improve independent quadrature.
                rem = mp.quad(
                    lambda t: mp.exp(-nmp*t)*t**(b-1)*(q(t)-mp.mpf("0.5")),
                    [0, 1, mp.inf]) / mp.gamma(b)
                q_laplace = mp.mpf("0.5")*nmp**(-b)+rem
                got = nmp**(-a)*(mp.zeta(b)-nmp**(1-b)/(b-1)-q_laplace)
            target = mp.fsum(mp.mpf(k)**(-b) for k in range(1, n))*nmp**(-a)
            rows.append({"a": a_s, "b": b_s, "n": n,
                         "target": mp.nstr(target, 40),
                         "absolute_error": mp.nstr(abs(got-target), 8)})
            assert abs(got-target) < mp.mpf("1e-55")
    return rows


def edge_checks():
    rows = []
    for b_s in ["0.2", "0.5", "0.8"]:
        b = mp.mpf(b_s)
        for eps_s in ["0.01", "0.001", "0.0001"]:
            eps = mp.mpf(eps_s)
            a = 1-b+eps
            tau = (mp.gamma(a)/((1-b)*(-mp.zeta(b))*mp.gamma(eps)))**(1/(1-b))
            T = bisect_crossing(a, b, tau)
            leading = (mp.gamma(1-b)*eps/((1-b)*(-mp.zeta(b))))**(1/(1-b))
            rows.append({"edge": "a+b=1", "b": b_s, "epsilon": eps_s,
                         "crossing_T": mp.nstr(T, 30),
                         "T_over_tau": mp.nstr(T/tau, 25),
                         "T_over_leading": mp.nstr(T/leading, 25),
                         "bound_for_one_minus_ratio_power": mp.nstr((1-b)*tau/eps, 10)})
    for b_s in ["1.5", "2", "3"]:
        b = mp.mpf(b_s)
        for a_s in ["0.001", "0.0001", "0.00001"]:
            a = mp.mpf(a_s)
            tau = ((b-1)*mp.gamma(a+b-1)*mp.zeta(b)/mp.gamma(a))**(1/(b-1))
            T = bisect_crossing(a, b, tau)
            leading = (mp.gamma(b)*mp.zeta(b)*a)**(1/(b-1))
            rows.append({"edge": "a=0,b>1", "a": a_s, "b": b_s,
                         "crossing_T": mp.nstr(T, 30),
                         "T_over_leading": mp.nstr(T/leading, 25)})
    for a_s in ["0.2", "0.1", "0.05", "0.02"]:
        a, b = mp.mpf(a_s), mp.mpf(1)
        sigma = mp.exp(mp.euler+mp.digamma(a))
        T = bisect_crossing(a, b, sigma)
        mass_leading = sigma**a/(a*a*mp.gamma(a))
        rows.append({"edge": "a=0,b=1", "a": a_s,
                     "crossing_T": mp.nstr(T, 30),
                     "T_over_sigma": mp.nstr(T/sigma, 25),
                     "e_times_a_times_mass_approximation": mp.nstr(mp.e*a*mass_leading, 25)})
    return rows


def angular_checks():
    # Independent finite defining-series roots strictly inside the disk.
    # No signed density, Hurwitz integral, or boundary layer is used here.
    rho = mp.mpf("0.75")
    rows = []
    for a_s, b_s in [("0.1", "0.9"), ("0.4", "0.8"),
                     ("0.4", "1"), ("0.4", "1.4"), ("0", "2.3")]:
        a, b = mp.mpf(a_s), mp.mpf(b_s)
        h = mp.mpf(0)
        coeff = []
        for n in range(1, 451):
            coeff.append((n, h*mp.mpf(n)**(-a)*rho**n))
            h += mp.mpf(n)**(-b)
        imag = lambda theta: mp.fsum(c*mp.sin(n*theta) for n, c in coeff)
        lo, hi = mp.acos(rho), mp.pi/2
        assert imag(lo) > 0 and imag(hi) < 0
        for _ in range(145):
            mid = (lo+hi)/2
            if imag(mid) > 0:
                lo = mid
            else:
                hi = mid
        theta = (lo+hi)/2
        rows.append({"a": a_s, "b": b_s, "rho": "0.75",
                     "theta": mp.nstr(theta, 35),
                     "lower_angle": mp.nstr(mp.acos(rho), 20),
                     "upper_angle": mp.nstr(mp.pi/2, 20)})
    return rows


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("subunit_diagnostics.json"))
    args = parser.parse_args()
    mp.mp.dps = 80
    data = {"arithmetic": "mpmath, 80 decimal digits",
            "scope": "Floating-point diagnostics; proofs are in subunit_kernel.tex.",
            "moment_checks": moment_checks(),
            "boundary_layers": edge_checks(),
            "interior_angular_roots": angular_checks()}
    args.output.write_text(json.dumps(data, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({"output": str(args.output),
                      "moment_checks": len(data["moment_checks"]),
                      "boundary_layer_checks": len(data["boundary_layers"]),
                      "angular_checks": len(data["interior_angular_roots"]),
                      "max_moment_error": max(float(r["absolute_error"])
                                              for r in data["moment_checks"])}))


if __name__ == "__main__":
    main()
