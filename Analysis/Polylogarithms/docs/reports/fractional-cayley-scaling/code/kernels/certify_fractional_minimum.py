#!/usr/bin/env python3
"""Exact certificate for positive quartic coefficient and a local minimum.

Uses the standard-library-only interval primitives in the companion
certify_fractional_turning.py. Every calculation below uses integer/Fraction
arithmetic; powers for the rational inner order b=999/1000 are enclosed with
the same proved logarithm/exponential bounds as the outer-order powers.
"""

from fractions import Fraction as F
from pathlib import Path
import json

from certify_fractional_turning import (
    BITS, LOG_TERMS, EXP_TERMS, I, log_integer, exp_interval,
    sqrt_interval, floor_f, ceil_f, decimal_fixed,
)


def coefficients(a, b, logs):
    p = {1: I.make(0)}
    h = I.make(0)
    for n in range(1, 8):
        if n >= 2:
            p[n] = h/exp_interval(a*logs[n])
        h += exp_interval(b*logs[n]).reciprocal()
    return p


def quantities(a, b, logs):
    p = coefficients(a, b, logs)
    mu = p[3]/(2*p[2])
    N = 4*p[3]*mu**2-4*p[4]*mu+p[5]
    K = -N/(2*p[2])
    Q0 = (p[7]-6*p[6]*mu+12*p[5]*mu**2-8*p[4]*mu**3)/(2*p[2])
    Q = Q0-(8*p[3]*mu-4*p[4])*K/(2*p[2])
    dmu = mu*(logs[2]-logs[3])
    dN = (4*(-logs[3]*p[3]*mu**2+2*p[3]*mu*dmu)
          -4*(-logs[4]*p[4]*mu+p[4]*dmu)-logs[5]*p[5])
    dK = -dN/(2*p[2])+logs[2]*K
    return {"eta0": mu, "K": K, "Q": Q, "Q_at_K_zero": Q0, "dK_da": dK}


def serialize(x):
    places = 36
    scale = 10**places
    lo = F(floor_f(x.lo*scale), scale)
    hi = F(ceil_f(x.hi*scale), scale)
    return {"lower": str(x.lo), "upper": str(x.hi),
            "decimal_lower": decimal_fixed(lo, places),
            "decimal_upper": decimal_fixed(hi, places)}


def main():
    b = F(999, 1000)
    lo = F(100057049936559087278, 100000000000000000000)
    hi = F(100057049936559087279, 100000000000000000000)
    logs = {n: log_integer(n) for n in range(1, 8)}
    at_lo = quantities(I.make(lo), I.make(b), logs)
    at_hi = quantities(I.make(hi), I.make(b), logs)
    entire = quantities(I.make(lo, hi), I.make(b), logs)
    assert at_lo["K"].lo > 0
    assert at_hi["K"].hi < 0
    assert entire["Q"].lo > 0
    assert entire["Q_at_K_zero"].lo > 0
    assert entire["dK_da"].hi < 0
    prefactor = sqrt_interval(-entire["dK_da"]/(2*entire["Q_at_K_zero"]))
    data = {
        "status": "Exact rational interval certificate; no floating-point arithmetic is used.",
        "b": str(b), "a_lower": str(lo), "a_upper": str(hi),
        "precision_bits": BITS, "log_terms": LOG_TERMS, "exp_terms": EXP_TERMS,
        "local_dependency": "certify_fractional_turning.py: exact outward interval arithmetic and elementary bounds",
        "K_at_lower": serialize(at_lo["K"]),
        "K_at_upper": serialize(at_hi["K"]),
        "quantities_throughout_interval": {k: serialize(v) for k, v in entire.items()},
        "turning_prefactor_sqrt_minus_Kprime_over_2Q": serialize(prefactor),
        "analytic_dependencies": [
            "The local-threshold theorem proves K has a unique zero a_star in (1,2) for every 0<b<1.",
            "The eta Taylor formula identifies Q as the quartic coefficient; at K=0 it equals Q_at_K_zero.",
            "Joint analyticity and the implicit-function theorem in t=rho^2 give a unique local branch of strict minima for a>a_star sufficiently close.",
            "Together with the negative-Q certificate at b=1/2 and continuity, this proves the existence of a quartic-sign zero for some 1/2<b<999/1000, but does not prove uniqueness."
        ]}
    path = Path(__file__).resolve().parents[2] / "data" / "kernels" / "fractional_minimum_certificate.json"
    path.write_text(json.dumps(data, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({
        "output": str(path),
        "K_at_lower": data["K_at_lower"]["decimal_lower"],
        "K_at_upper": data["K_at_upper"]["decimal_upper"],
        "Q_range": [data["quantities_throughout_interval"]["Q"]["decimal_lower"],
                    data["quantities_throughout_interval"]["Q"]["decimal_upper"]],
        "Kprime_range": [data["quantities_throughout_interval"]["dK_da"]["decimal_lower"],
                         data["quantities_throughout_interval"]["dK_da"]["decimal_upper"]],
        "turning_prefactor": [data["turning_prefactor_sqrt_minus_Kprime_over_2Q"]["decimal_lower"],
                              data["turning_prefactor_sqrt_minus_Kprime_over_2Q"]["decimal_upper"]]}))


if __name__ == "__main__":
    main()
