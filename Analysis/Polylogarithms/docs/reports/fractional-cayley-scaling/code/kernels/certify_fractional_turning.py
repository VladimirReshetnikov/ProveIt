#!/usr/bin/env python3
"""Exact certificate for a fractional normalized-radius turning branch.

Standard-library integer/Fraction arithmetic only. The certificate proves
opposite signs of K at two rational outer orders, and Q<0 throughout the
interval between them, at b=1/2. Analytic uniqueness of the K-zero is a
separate theorem; the local turning branch then follows by the analytic
implicit-function theorem applied in t=rho^2.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
import json

BITS = 128
SCALE = 1 << BITS
LOG_TERMS = 120
EXP_TERMS = 60


def floor_f(x):
    return x.numerator // x.denominator


def ceil_f(x):
    return -((-x.numerator) // x.denominator)


def round_lower(x):
    return F(floor_f(x*SCALE), SCALE)


def round_upper(x):
    return F(ceil_f(x*SCALE), SCALE)


@dataclass(frozen=True)
class I:
    lo: F
    hi: F

    def __post_init__(self):
        assert self.lo <= self.hi

    @staticmethod
    def make(lo, hi=None):
        lo = F(lo)
        hi = lo if hi is None else F(hi)
        return I(round_lower(lo), round_upper(hi))

    @staticmethod
    def coerce(x):
        return x if isinstance(x, I) else I.make(x)

    def __add__(self, other):
        other = I.coerce(other)
        return I.make(self.lo+other.lo, self.hi+other.hi)

    __radd__ = __add__

    def __neg__(self):
        return I(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + (-I.coerce(other))

    def __rsub__(self, other):
        return I.coerce(other)+(-self)

    def __mul__(self, other):
        other = I.coerce(other)
        products = [x*y for x in (self.lo, self.hi)
                    for y in (other.lo, other.hi)]
        return I.make(min(products), max(products))

    __rmul__ = __mul__

    def reciprocal(self):
        assert self.lo*self.hi > 0
        return I.make(1/self.hi, 1/self.lo)

    def __truediv__(self, other):
        return self*I.coerce(other).reciprocal()

    def __rtruediv__(self, other):
        return I.coerce(other)*self.reciprocal()

    def __pow__(self, power):
        assert isinstance(power, int) and power >= 0
        ans = I.make(1)
        base = self
        while power:
            if power & 1:
                ans = ans*base
            power //= 2
            if power:
                base = base*base
        return ans


def log_integer(n):
    """2 atanh((n-1)/(n+1)), with a rational positive-series tail."""
    if n == 1:
        return I.make(0)
    z = F(n-1, n+1)
    power = z
    total = F(0)
    for j in range(LOG_TERMS):
        total += 2*power/(2*j+1)
        power *= z*z
    tail = 2*power/((2*LOG_TERMS+1)*(1-z*z))
    return I.make(total, total+tail)


def exp_at_rational(x):
    """Positive Taylor series with first-omitted-term geometric bound."""
    assert x >= 0 and x < EXP_TERMS+2
    total = F(1)
    term = F(1)
    for j in range(1, EXP_TERMS+1):
        term *= x/j
        total += term
    omitted = term*x/(EXP_TERMS+1)
    upper_tail = omitted/(1-x/(EXP_TERMS+2))
    return I.make(total, total+upper_tail)


def exp_interval(x):
    assert x.lo >= 0
    return I.make(exp_at_rational(x.lo).lo, exp_at_rational(x.hi).hi)


def sqrt_rational(x):
    assert x >= 0
    n = isqrt((x.numerator*SCALE*SCALE)//x.denominator)
    return I.make(F(n, SCALE), F(n+1, SCALE))


def sqrt_interval(x):
    return I.make(sqrt_rational(x.lo).lo, sqrt_rational(x.hi).hi)


def coefficients(a, logs):
    p = {1: I.make(0)}
    h = I.make(0)
    for n in range(1, 8):
        if n >= 2:
            p[n] = h/exp_interval(a*logs[n])
        h += sqrt_rational(F(n)).reciprocal()
    return p


def quantities(a, logs):
    p = coefficients(a, logs)
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


def decimal_fixed(x, places=24):
    scale = 10**places
    n = floor_f(x*scale)
    sign = "-" if n < 0 else ""
    n = abs(n)
    return f"{sign}{n//scale}.{n%scale:0{places}d}"


def serialize_interval(x):
    # Decimal endpoints rounded outward, in addition to exact fractions.
    dscale = 10**24
    lower = F(floor_f(x.lo*dscale), dscale)
    upper = F(ceil_f(x.hi*dscale), dscale)
    return {"lower": str(x.lo), "upper": str(x.hi),
            "decimal_lower": decimal_fixed(lower),
            "decimal_upper": decimal_fixed(upper)}


def main():
    lo = F(131298577512189, 100000000000000)
    hi = F(131298577512190, 100000000000000)
    logs = {n: log_integer(n) for n in range(1, 8)}
    at_lo = quantities(I.make(lo), logs)
    at_hi = quantities(I.make(hi), logs)
    entire = quantities(I.make(lo, hi), logs)
    assert at_lo["K"].lo > 0
    assert at_hi["K"].hi < 0
    assert entire["Q"].hi < 0
    assert entire["Q_at_K_zero"].hi < 0
    assert entire["dK_da"].hi < 0
    turning_prefactor = sqrt_interval(entire["dK_da"]/(2*entire["Q_at_K_zero"]))
    data = {
        "status": "Exact rational interval certificate; no floating-point arithmetic is used.",
        "b": "1/2", "a_lower": str(lo), "a_upper": str(hi),
        "precision_bits": BITS, "log_terms": LOG_TERMS, "exp_terms": EXP_TERMS,
        "K_at_lower": serialize_interval(at_lo["K"]),
        "K_at_upper": serialize_interval(at_hi["K"]),
        "quantities_throughout_interval": {k: serialize_interval(v) for k,v in entire.items()},
        "turning_prefactor_sqrt_Kprime_over_2Q": serialize_interval(turning_prefactor),
        "analytic_dependencies": [
            "The local-threshold theorem proves K has a unique zero a_star in (1,2) at b=1/2.",
            "The eta Taylor formula identifies the displayed interval Q with the quartic coefficient.",
            "The analytic implicit-function theorem in t=rho^2 turns these certified signs into a branch of strict local maxima for a<a_star sufficiently close."
        ],
    }
    path = Path(__file__).resolve().parents[2] / "data" / "kernels" / "fractional_turning_certificate.json"
    path.write_text(json.dumps(data, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({"output": str(path),
                      "K_at_lower": data["K_at_lower"]["decimal_lower"],
                      "K_at_upper": data["K_at_upper"]["decimal_upper"],
                      "Q_range": [data["quantities_throughout_interval"]["Q"]["decimal_lower"],
                                  data["quantities_throughout_interval"]["Q"]["decimal_upper"]],
                      "turning_prefactor": [data["turning_prefactor_sqrt_Kprime_over_2Q"]["decimal_lower"],
                                            data["turning_prefactor_sqrt_Kprime_over_2Q"]["decimal_upper"]]}))


if __name__ == "__main__":
    main()
