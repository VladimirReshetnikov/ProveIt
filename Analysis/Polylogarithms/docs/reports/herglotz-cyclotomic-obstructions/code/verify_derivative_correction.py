#!/usr/bin/env python3
"""Independent numerical checks of the corrected even-q derivative formula.

Requires mpmath.  This program supplies supporting numerical evidence, not
an interval proof.  Its reference value uses the positive Binet derivative
integral, not a finite difference or the finite Clausen sum being checked:

 F'(x) = zeta(2)/(2*x**2)
         + 4*x*integral_0^inf u*Lambda(u)/(x**2+u**2)**2 du,
 Lambda(u) = -sum_{n>=1} log(1-exp(-2*pi*n*u)).

The eta modular transformation accelerates Lambda near zero.  The same
positive integral and the absolutely convergent Fourier definition of Cl_2
justify the mathematical formulas separately from these numerical checks.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import mpmath as mp


def lambert_large(u):
    assert u >= 1
    total = mp.mpf(0)
    n = 1
    while True:
        term = -mp.log1p(-mp.exp(-2*mp.pi*n*u))
        total += term
        if term < mp.eps**2:
            return total
        n += 1


def lambert(u):
    if u >= 1:
        return lambert_large(u)
    # eta(i/u) = sqrt(u)*eta(i*u).
    return mp.pi/(12*u) + mp.log(u)/2 - mp.pi*u/12 + lambert_large(1/u)


def binet_derivative(x):
    def integrand(u):
        if u == 0:
            return mp.pi/(12*x**4)
        return u*lambert(u)/(x*x+u*u)**2
    integral = mp.quad(integrand, [0, x, 1, mp.inf])
    return mp.zeta(2)/(2*x*x) + 4*x*integral


def cl2(theta):
    return mp.im(mp.polylog(2, mp.exp(1j*theta)))


def w_star(q):
    # The midpoint k=q/2 is OMITTED, rather than evaluated numerically.
    return mp.fsum(mp.cot(2*mp.pi*k/q)*cl2(2*mp.pi*k/q)
                   for k in range(1, q) if 2*k != q)


def verify(dps):
    mp.mp.dps = dps
    records = []
    for q in (4, 6, 8, 12):
        x = mp.mpf(2)/q
        reference = binet_derivative(x)
        w = w_star(q)
        # x*F'(x)-(1+log(2)) = pi^2*(q^2-4)/(24q)+W*(q)-log(2).
        polynomial = mp.pi**2*(q*q-4)/(24*q)
        corrected = (1+polynomial+w)/x
        # If the midpoint's continuous limit is included in W and the
        # displayed -log(2) is still appended, log(2) is counted twice.
        double_counted = corrected-mp.log(2)/x
        error = reference-corrected
        assert abs(error) < mp.mpf(10)**(-dps+8), (q, error)
        assert abs((reference-double_counted)-mp.log(2)/x) < mp.mpf(10)**(-dps+8)
        records.append({
            "q": q,
            "x": f"2/{q}",
            "binet_derivative": mp.nstr(reference, dps-5),
            "W_star": mp.nstr(w, dps-5),
            "corrected_rhs": mp.nstr(corrected, dps-5),
            "numerical_residual": mp.nstr(error, 8),
            "double_counted_rhs_error": mp.nstr(reference-double_counted, dps-5),
            "predicted_double_counted_error": f"({q}/2)*log(2)",
        })

    limits = []
    for exponent in (8, 16, 20):
        h = mp.mpf(10)**(-exponent)
        value = mp.cot(mp.pi+h)*cl2(mp.pi+h)
        limits.append({"h": f"1e-{exponent}",
                       "value": mp.nstr(value, dps-5),
                       "value_plus_log_2": mp.nstr(value+mp.log(2), 10)})

    elementary = mp.mpf(2)+mp.pi**2/4
    assert abs(binet_derivative(mp.mpf('0.5'))-elementary) < mp.mpf(10)**(-dps+8)
    return {
        "status": "passed",
        "evidence_type": "independent_high_precision_numerical_check_not_interval_proof",
        "working_decimal_digits": dps,
        "definition": "W_star(q) omits k=q/2 when q is even",
        "corrected_formula": "(2/q)*F_prime(2/q)-(1+log(2)) = pi^2*(q^2-4)/(24*q)+W_star(q)-[2 divides q]*log(2)",
        "midpoint_limit": "lim_{theta->pi} cot(theta)*Cl_2(theta) = -log(2)",
        "exact_limit_reason": "Cl_2(pi)=0 and Cl_2_prime(pi)=-log(2), while cot(pi+h)=1/h+O(h)",
        "elementary_example": "F_prime(1/2)=2+pi^2/4",
        "records": records,
        "limit_checks": limits,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dps", type=int, default=65)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.dps < 40:
        parser.error("Use at least 40 working decimal digits")
    result = verify(args.dps)
    destination = args.output or Path(__file__).resolve().parents[1]/"data"/"derivative_correction_checks.json"
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({"status": result["status"], "working_decimal_digits": args.dps,
                      "q_values": [row["q"] for row in result["records"]],
                      "output": str(destination)}))
