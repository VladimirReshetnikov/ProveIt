#!/usr/bin/env python3
"""Evaluate the explicit first correction by numerical differentiation.

Derivatives vary the interval's left endpoint u while holding f fixed.
This computes c_rel and c_full only, not an all-orders recursion.
The float64 cosine transforms and sums are not interval-certified.
"""

import argparse
from decimal import Decimal, localcontext
from fractions import Fraction
import json

import mpmath as mp
import numpy as np

from check_shift import cosine_coefficients
from density import critical_shift, density, endpoint


def coefficient(s, M=256, dps=45):
    """Evaluate U'(a), U''(a), S'(a), and the two correction normalizations."""
    if M < 8 or dps < 25:
        raise ValueError("Use M >= 8 and dps >= 25.")
    with mp.workdps(dps):
        slope = Fraction(str(s))
        s = mp.mpf(slope.numerator) / slope.denominator
        if s <= critical_shift():
            raise ValueError("The Apéry correction replay requires s > s*.")
        a = (s / (s + 2))**2

        def f(t):
            C = endpoint()
            return mp.log(C * density(C*t) / mp.sqrt(1-t))

        values, derivatives, seconds = [], [], []
        for j in range(M):
            theta = mp.pi * (mp.mpf(j) + mp.mpf("0.5")) / M
            eta = mp.sin(theta/2)**2  # partial t(theta;u) / partial u
            t = (1+a)/2 + (1-a)*mp.cos(theta)/2
            values.append(float(f(t)))
            derivatives.append(float(mp.diff(f, t)*eta))
            seconds.append(float(mp.diff(f, t, 2)*eta**2))
        v = cosine_coefficients(values)
        vd = cosine_coefficients(derivatives)
        Up = mp.mpf(str(vd[0]))
        Upp = mp.mpf(str(np.mean(seconds)))
        Sp = mp.mpf(str(2 * sum(k*v[k]*vd[k] for k in range(1, M))))
        D = 2*a**mp.mpf("1.5")*(1-a)*Up/s
        relative = (D*Sp/6 + D*Up/8
                    + D/24*(1/(1-a) + mp.mpf("1.5")/a)
                    + a**mp.mpf("1.5")*((1-a)*Upp-Up)/(12*s))
        full = relative - (1 + 1/(s+1) - 1/(s+2))/48
        endpoint_energy = -(1-a)*Up**2/2
        simplified = (mp.sqrt(a)*(1-a)/(24*s)
                      * (-4*a*(1-a)*Up**3 + 6*a*Up**2 + 3*Up + 2*a*Upp))
        return {
            "s": str(s), "nodes": M, "dps": dps,
            "U_prime": str(Up), "U_second": str(Upp), "S_prime": str(Sp),
            "c_rel": mp.nstr(relative, 20), "c_full": mp.nstr(full, 20),
            "S_prime_endpoint_identity": mp.nstr(endpoint_energy, 20),
            "S_prime_identity_residual": mp.nstr(Sp-endpoint_energy, 12),
            "c_rel_simplified": mp.nstr(simplified, 20),
            "c_rel_formula_difference": mp.nstr(relative-simplified, 12),
            "status": "numerical quadrature and differentiation, not certified",
        }


def corrected_residuals(numerics, correction):
    """Subtract c_rel/N from the stored logarithmic residual.

    Decimal arithmetic preserves the supplied decimal strings. It cannot
    improve the accuracy of the numerical values those strings represent.
    """
    checks = []
    with localcontext() as context:
        context.prec = 60
        c = Decimal(correction["c_rel"])
        for check in numerics["checks"]:
            N = check["N"]
            leading = Decimal(check["log_relative_error"])
            corrected = leading - c/N
            checks.append({
                "N": N, "leading_log_error": str(leading),
                "corrected_log_error": str(corrected),
                "N_squared_corrected_error": str(N*N*corrected),
            })
    return {"status": "floating-point comparison, not interval-certified",
            "c_rel": correction["c_rel"], "checks": checks}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--s", default="1")
    parser.add_argument("--M", type=int, default=256)
    parser.add_argument("--dps", type=int, default=45)
    args = parser.parse_args()
    print(json.dumps(coefficient(args.s, args.M, args.dps), indent=2))


if __name__ == "__main__":
    main()
