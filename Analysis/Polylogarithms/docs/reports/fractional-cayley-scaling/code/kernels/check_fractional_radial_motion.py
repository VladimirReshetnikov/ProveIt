#!/usr/bin/env python3
"""Exploration of fractional-order normalized radial motion.

Every numerical row is a diagnostic, not an interval certificate. The
defining disk series is used with an explicit analytic truncation budget
for both F and zF'. Floating-point rounding is not enclosed.
"""

from __future__ import annotations

import json
from pathlib import Path

import mpmath as mp


def nterms(rho, target):
    n = int(mp.ceil(mp.log(target*(1-rho)**2)/mp.log(rho)))
    while rho**(n+1)*((n+1)-n*rho)/(1-rho)**2 > target:
        n += 1
    return n


def coefficients(a, b, n):
    coeff = [mp.mpf(0), mp.mpf(0)]
    h = mp.mpf(1)
    for j in range(2, n+1):
        coeff.append(h*mp.mpf(j)**(-a))
        h += mp.mpf(j)**(-b)
    return coeff


def polynomial_and_derivative(coeff, z, n):
    value = mp.mpc(coeff[n])
    deriv = mp.mpc(0)
    for j in range(n-1, -1, -1):
        deriv = deriv*z + value
        value = value*z + coeff[j]
    return value, deriv


def local_quantities(a, b):
    A = 1+mp.power(2, -b)
    B = A+mp.power(3, -b)
    C = B+mp.power(4, -b)
    eta0 = A*mp.power(mp.mpf(2)/3, a)/2
    K = (A*B*mp.power(mp.mpf(1)/3, a)
         - C*mp.power(mp.mpf(2)/5, a)/2
         - A**3*mp.power(mp.mpf(8)/27, a)/2)
    return eta0, K


def quartic_local_coefficient(a, b):
    eta0, K = local_quantities(a, b)
    p = {}
    h = mp.mpf(0)
    for n in range(1, 8):
        p[n] = h*mp.mpf(n)**(-a)
        h += mp.mpf(n)**(-b)
    return -((8*p[3]*eta0-4*p[4])*K
             + 8*p[4]*eta0**3-12*p[5]*eta0**2
             + 6*p[6]*eta0-p[7])/(2*p[2])


def solve_row(a, b, rho, coeff):
    target = mp.mpf("1e-50")
    n = nterms(rho, target)
    eta0, K = local_quantities(a, b)
    theta = mp.acos(rho*eta0)
    lo, hi = mp.acos(rho), mp.pi/2
    for iteration in range(30):
        z = rho*mp.exp(mp.j*theta)
        F, dF = polynomial_and_derivative(coeff, z, n)
        H = z*dF
        residual = F.imag
        if abs(residual) < mp.mpf("1e-57"):
            break
        if residual > 0:
            lo = theta
        else:
            hi = theta
        candidate = theta-residual/H.real
        theta = candidate if lo < candidate < hi else (lo+hi)/2
    else:
        raise RuntimeError("Newton iteration did not converge")
    eta = mp.cos(theta)/rho
    # S_theta = Re(zF'), S_rho = Im(zF')/rho.
    # Implicit differentiation of S(rho,theta(rho))=0 gives this value.
    derivative = (mp.sin(theta)*H.imag/H.real-mp.cos(theta))/rho**2
    F_tail = rho**(n+1)/(1-rho)
    H_tail = rho**(n+1)*((n+1)-n*rho)/(1-rho)**2
    return {
        "rho": mp.nstr(rho, 8), "theta": mp.nstr(theta, 40),
        "eta": mp.nstr(eta, 40), "eta_minus_eta0": mp.nstr(eta-eta0, 30),
        "d_eta_d_rho": mp.nstr(derivative, 35),
        "quadratic_local_coefficient_K": mp.nstr(K, 30),
        "eta0": mp.nstr(eta0, 40),
        "series_terms": n,
        "absolute_F_truncation_bound": mp.nstr(F_tail, 8),
        "absolute_zFprime_truncation_bound": mp.nstr(H_tail, 8),
        "floating_point_equation_residual": mp.nstr(abs(residual), 8),
        "angular_slope": mp.nstr(H.real, 20),
        "newton_iterations": iteration+1,
    }


def main():
    mp.mp.dps = 70
    radii = [mp.mpf(s) for s in ["0.3", "0.7", "0.9", "0.98"]]
    max_terms = nterms(max(radii), mp.mpf("1e-50"))
    groups = []
    for b_text in ["0.25", "0.5", "0.75"]:
        b = mp.mpf(b_text)
        A = 1+mp.power(2, -b)
        B = A+mp.power(3, -b)
        C = B+mp.power(4, -b)
        G = lambda a: (C+A**3*mp.power(mp.mpf(20)/27, a)
                       -2*A*B*mp.power(mp.mpf(5)/6, a))
        threshold = mp.findroot(G, (1, 2))
        for delta_text in ["-0.02", "-0.0001", "0", "0.02"]:
            a = threshold+mp.mpf(delta_text)
            coeff = coefficients(a, b, max_terms)
            rows = [solve_row(a, b, rho, coeff) for rho in radii]
            group = {"a": mp.nstr(a, 45), "b": b_text,
                     "local_threshold_a_star": mp.nstr(threshold, 45),
                     "a_minus_local_threshold": delta_text,
                     "quartic_local_coefficient_L": mp.nstr(quartic_local_coefficient(a, b), 35),
                     "rows": rows}
            groups.append(group)
            print(json.dumps({"b": b_text, "delta": delta_text,
                              "a": mp.nstr(a, 18),
                              "derivatives": [r["d_eta_d_rho"] for r in rows]}),
                  flush=True)
    data = {
        "scope": "Diagnostics only; analytic disk-series truncation bounds are explicit, but rounding is not interval-enclosed.",
        "arithmetic": "mpmath, 70 decimal digits",
        "tail_bound_justification": "For a>=1,b>0, H_(n-1)^(b)/n^a <= 1. Therefore tails are bounded by sum rho^n and sum n rho^n.",
        "groups": groups,
    }
    out = Path(__file__).resolve().parents[2] / "data" / "kernels" / "fractional_radial_diagnostics.json"
    out.write_text(json.dumps(data, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({"output": str(out), "rows": sum(len(g["rows"]) for g in groups)}))


if __name__ == "__main__":
    main()
