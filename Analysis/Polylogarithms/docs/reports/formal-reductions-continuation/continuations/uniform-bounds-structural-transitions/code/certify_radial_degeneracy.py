#!/usr/bin/env python3
"""Exact rational certificate for an isolated K=Q=0 radial degeneracy.

All sign decisions use Fraction arithmetic with outward dyadic rounding.
The interval primitives adapt the repository's certify_fractional_turning.py
at Analysis/Polylogarithms/docs/reports/fractional-cayley-scaling/code/kernels,
with higher precision and first-order interval automatic differentiation.
No numerical root finder or floating-point arithmetic is used by this file.

Run: python certify_radial_degeneracy.py
Output: radial_degeneracy_certificate.json beside this file.
"""

from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as F
from pathlib import Path
import json

BITS = 192
SCALE = 1 << BITS
LOG_TERMS = 360
EXP_TERMS = 100


def floor_f(x):
    return x.numerator // x.denominator


def ceil_f(x):
    return -((-x.numerator) // x.denominator)


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
        return I(F(floor_f(lo*SCALE), SCALE),
                 F(ceil_f(hi*SCALE), SCALE))

    @staticmethod
    def coerce(x):
        return x if isinstance(x, I) else I.make(x)

    def __add__(self, other):
        other = I.coerce(other)
        return I.make(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __neg__(self):
        return I(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + (-I.coerce(other))

    def __rsub__(self, other):
        return I.coerce(other) + (-self)

    def __mul__(self, other):
        other = I.coerce(other)
        p = [x*y for x in (self.lo, self.hi)
             for y in (other.lo, other.hi)]
        return I.make(min(p), max(p))

    __rmul__ = __mul__

    def reciprocal(self):
        assert self.lo*self.hi > 0
        return I.make(1/self.hi, 1/self.lo)

    def __truediv__(self, other):
        return self * I.coerce(other).reciprocal()

    def __rtruediv__(self, other):
        return I.coerce(other) * self.reciprocal()

    def __pow__(self, n):
        assert isinstance(n, int) and n >= 0
        out, base = I.make(1), self
        while n:
            if n & 1:
                out = out * base
            n //= 2
            if n:
                base = base * base
        return out


def log_integer(n):
    """2 atanh((n-1)/(n+1)), bounded by its positive series tail."""
    if n == 1:
        return I.make(0)
    z = F(n-1, n+1)
    power, total = z, F(0)
    for j in range(LOG_TERMS):
        total += 2*power/(2*j+1)
        power *= z*z
    tail = 2*power/((2*LOG_TERMS+1)*(1-z*z))
    return I.make(total, total+tail)


def exp_at_rational(x):
    """Positive Taylor series and a geometric omitted-tail majorant."""
    assert 0 <= x < 3
    total, term = F(1), F(1)
    for j in range(1, EXP_TERMS+1):
        term *= x/j
        total += term
    omitted = term*x/(EXP_TERMS+1)
    tail = omitted/(1-x/(EXP_TERMS+2))
    return I.make(total, total+tail)


def exp_interval(x):
    return I.make(exp_at_rational(x.lo).lo,
                  exp_at_rational(x.hi).hi)


@dataclass(frozen=True)
class Jet:
    """Value and both first partial derivatives, all interval enclosed."""
    v: I
    da: I
    db: I

    @staticmethod
    def coerce(x):
        return x if isinstance(x, Jet) else Jet(I.coerce(x), I.make(0), I.make(0))

    def __add__(self, other):
        other = Jet.coerce(other)
        return Jet(self.v+other.v, self.da+other.da, self.db+other.db)

    __radd__ = __add__

    def __neg__(self):
        return Jet(-self.v, -self.da, -self.db)

    def __sub__(self, other):
        return self + (-Jet.coerce(other))

    def __rsub__(self, other):
        return Jet.coerce(other) + (-self)

    def __mul__(self, other):
        other = Jet.coerce(other)
        return Jet(self.v*other.v,
                   self.da*other.v+self.v*other.da,
                   self.db*other.v+self.v*other.db)

    __rmul__ = __mul__

    def reciprocal(self):
        v = self.v.reciprocal()
        return Jet(v, -self.da*v*v, -self.db*v*v)

    def __truediv__(self, other):
        return self * Jet.coerce(other).reciprocal()

    def __rtruediv__(self, other):
        return Jet.coerce(other) * self.reciprocal()

    def __pow__(self, n):
        assert isinstance(n, int) and n >= 0
        out, base = Jet.coerce(1), self
        while n:
            if n & 1:
                out = out * base
            n //= 2
            if n:
                base = base * base
        return out


def coefficients(a, b, logs):
    p = {}
    h, dh = I.make(0), I.make(0)
    for n in range(1, 10):
        if n >= 2:
            g = exp_interval(a*logs[n]).reciprocal()
            pn = h*g
            p[n] = Jet(pn, -logs[n]*pn, dh*g)
        x = exp_interval(b*logs[n]).reciprocal()
        h += x
        dh -= logs[n]*x
    return p


def quantities(a, b, logs):
    p = coefficients(a, b, logs)
    mu = p[3]/(2*p[2])
    B1 = 4*p[3]*mu**2 - 4*p[4]*mu + p[5]
    B1p = 8*p[3]*mu - 4*p[4]
    B2 = 8*p[4]*mu**3 - 12*p[5]*mu**2 + 6*p[6]*mu - p[7]
    B2p = 24*p[4]*mu**2 - 24*p[5]*mu + 6*p[6]
    B3 = (16*p[5]*mu**4 - 32*p[6]*mu**3 + 24*p[7]*mu**2
          - 8*p[8]*mu + p[9])
    K = -B1/(2*p[2])
    Q = -(B1p*K+B2)/(2*p[2])
    R = -(B1p*Q+4*p[3]*K**2+B2p*K+B3)/(2*p[2])
    qprime = Q.db - Q.da*K.db/K.da
    determinant = K.da*Q.db-K.db*Q.da
    return {"mu": mu.v, "K": K.v, "Q": Q.v, "R": R.v,
            "K_a": K.da, "K_b": K.db, "Q_a": Q.da, "Q_b": Q.db,
            "qprime_along_K_zero": qprime,
            "jacobian_KQ": determinant}


def decimal_fixed(n, places):
    sign = "-" if n < 0 else ""
    n = abs(n)
    scale = 10**places
    return f"{sign}{n//scale}.{n%scale:0{places}d}"


def serialize(x, places=42):
    scale = 10**places
    return {"lower": str(x.lo), "upper": str(x.hi),
            "decimal_lower": decimal_fixed(floor_f(x.lo*scale), places),
            "decimal_upper": decimal_fixed(ceil_f(x.hi*scale), places)}


def main():
    logs = {n: log_integer(n) for n in range(1, 10)}
    bl = F("0.99749378987342042107")
    bh = F("0.99749378987342042108")
    # Fine a brackets for the K-zero at the two rational b endpoints.
    al_at_bl = F("1.00143018096149513813198112513591610363")
    ah_at_bl = F("1.00143018096149513813198112513591610365")
    al_at_bh = F("1.00143018096149513812627198907246165442")
    ah_at_bh = F("1.00143018096149513812627198907246165445")
    endpoint_data = []
    for b, al, ah, qsign in [(bl, al_at_bl, ah_at_bl, -1),
                            (bh, al_at_bh, ah_at_bh, 1)]:
        at_l = quantities(I.make(al), I.make(b), logs)
        at_h = quantities(I.make(ah), I.make(b), logs)
        between = quantities(I.make(al, ah), I.make(b), logs)
        assert at_l["K"].lo > 0
        assert at_h["K"].hi < 0
        if qsign < 0:
            assert between["Q"].hi < 0
        else:
            assert between["Q"].lo > 0
        endpoint_data.append({"b": str(b), "a_lower": str(al), "a_upper": str(ah),
                              "K_at_a_lower": serialize(at_l["K"]),
                              "K_at_a_upper": serialize(at_h["K"]),
                              "Q_on_a_bracket": serialize(between["Q"])})
    # K_a,K_b<0 give confinement of a_*(b) to this rectangle.
    # The qprime certificate then gives strict monotonicity on that branch.
    rectangle_al = F("1.00143018096149513812")
    rectangle_ah = F("1.00143018096149513814")
    assert rectangle_al < al_at_bh < ah_at_bh < al_at_bl < ah_at_bl < rectangle_ah
    entire = quantities(I.make(rectangle_al, rectangle_ah), I.make(bl, bh), logs)
    assert entire["K_a"].hi < 0
    assert entire["K_b"].hi < 0
    assert entire["Q_a"].hi < 0
    assert entire["qprime_along_K_zero"].lo > 0
    assert entire["jacobian_KQ"].hi < 0
    assert entire["R"].hi < 0
    # Displayed simplified rational enclosures, independently checked here.
    advertised = {
        "R": (F("-3.368745e-11"), F("-3.368744e-11")),
        "qprime_along_K_zero": (F("4.87028e-8"), F("4.87029e-8")),
        "jacobian_KQ": (F("-8.31515e-10"), F("-8.31513e-10")),
        "K_a": (F("-0.017073210967"), F("-0.017073210965")),
        "K_b": (F("-0.009747328446"), F("-0.009747328443")),
        "Q_a": (F("-0.002284745315"), F("-0.002284745313")),
    }
    for name, (lo, hi) in advertised.items():
        assert lo < entire[name].lo <= entire[name].hi < hi
    fourth_power_prefactor = entire["K_a"]/(3*entire["R"])
    prefactor_lower, prefactor_upper = F("114.006986"), F("114.006989")
    assert prefactor_lower**4 < fourth_power_prefactor.lo
    assert fourth_power_prefactor.hi < prefactor_upper**4
    out = {
        "status": "Exact rational interval certificate; no floating-point sign decisions.",
        "arithmetic": {"bits": BITS, "log_terms": LOG_TERMS, "exp_terms": EXP_TERMS},
        "rectangle": {"a_lower": str(rectangle_al), "a_upper": str(rectangle_ah),
                      "b_lower": str(bl), "b_upper": str(bh)},
        "threshold_endpoints": endpoint_data,
        "quantities_throughout_rectangle": {k: serialize(v) for k,v in entire.items()},
        "advertised_enclosures": {k: [str(lo), str(hi)] for k,(lo,hi) in advertised.items()},
        "quarter_power_prefactor": {
            "lower": str(prefactor_lower), "upper": str(prefactor_upper),
            "fourth_power_enclosure": serialize(fourth_power_prefactor),
            "method": "Positive rational fourth powers bracket K_a/(3R)."
        },
        "scope": [
            "There is exactly one simultaneous zero K=Q=0 inside the certified rectangle.",
            "The sixth radial coefficient R is strictly negative there.",
            "The map (a,b) -> (K,Q) has nonzero Jacobian there.",
            "Uniqueness is local to this rectangle, not a global classification on 0<b<1.",
            "Analytic consequences (quarter-power turning branch and a region with two radial extrema) are proved in the accompanying article."
        ]
    }
    path = Path(__file__).resolve().parents[1]/"data"/"radial_degeneracy_certificate.json"
    path.write_text(json.dumps(out, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({"certificate": str(path), "rectangle": out["rectangle"],
                      "certified": out["advertised_enclosures"]}, indent=2))


if __name__ == "__main__":
    main()
