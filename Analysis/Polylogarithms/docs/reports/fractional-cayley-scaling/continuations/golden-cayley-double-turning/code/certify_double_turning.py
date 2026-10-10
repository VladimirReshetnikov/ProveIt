#!/usr/bin/env python3
"""Exact certificate for a double radial turning-point bifurcation.

Only integer and Fraction arithmetic is used. This is a self-contained
extension of the rational-interval method in the ProveIt report
fractional-cayley-scaling/code/kernels/certify_fractional_turning.py.
No assertion depends on floating-point discovery or external libraries.

The certificate proves a unique solution of K=Q=0 in the specified
rectangle, with negative sextic coefficient R and nonsingular (K,Q)
parameter map. The written analytic argument uses the intermediate value
theorem and the implicit function theorem to obtain two turning points.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as F
from pathlib import Path
import json

BITS = 256
SCALE = 1 << BITS
LOG_TERMS = 440
EXP_TERMS = 90


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

    def __pow__(self, n):
        assert isinstance(n, int) and n >= 0
        ans = I.make(1)
        base = self
        while n:
            if n & 1:
                ans = ans*base
            n //= 2
            if n:
                base = base*base
        return ans


def log_integer(n):
    """log(n)=2*atanh((n-1)/(n+1)), with positive-series tail."""
    assert isinstance(n, int) and 1 <= n <= 9
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


def exp_rational(x):
    """Positive Taylor series, bounded by a geometric omitted tail."""
    assert 0 <= x < 3
    term = F(1)
    total = F(1)
    for j in range(1, EXP_TERMS+1):
        term *= x/j
        total += term
    omitted = term*x/(EXP_TERMS+1)
    tail = omitted/(1-x/(EXP_TERMS+2))
    return I.make(total, total+tail)


def exp_interval(x):
    return I.make(exp_rational(x.lo).lo, exp_rational(x.hi).hi)


@dataclass(frozen=True)
class J:
    """A function value and two first derivatives, all enclosed by I."""
    v: I
    da: I
    db: I

    @staticmethod
    def make(v, da=0, db=0):
        return J(I.coerce(v), I.coerce(da), I.coerce(db))

    @staticmethod
    def coerce(x):
        return x if isinstance(x, J) else J.make(x)

    def __add__(self, other):
        other = J.coerce(other)
        return J(self.v+other.v, self.da+other.da, self.db+other.db)

    __radd__ = __add__

    def __neg__(self):
        return J(-self.v, -self.da, -self.db)

    def __sub__(self, other):
        return self + (-J.coerce(other))

    def __rsub__(self, other):
        return J.coerce(other)+(-self)

    def __mul__(self, other):
        other = J.coerce(other)
        return J(self.v*other.v,
                 self.da*other.v+self.v*other.da,
                 self.db*other.v+self.v*other.db)

    __rmul__ = __mul__

    def reciprocal(self):
        v = self.v.reciprocal()
        return J(v, -self.da*v*v, -self.db*v*v)

    def __truediv__(self, other):
        return self*J.coerce(other).reciprocal()

    def __rtruediv__(self, other):
        return J.coerce(other)*self.reciprocal()

    def __pow__(self, n):
        assert isinstance(n, int) and n >= 0
        if n == 0:
            return J.make(1)
        vn = self.v**n
        factor = n*self.v**(n-1)
        return J(vn, factor*self.da, factor*self.db)


def exp_jet(x):
    v = exp_interval(x.v)
    return J(v, v*x.da, v*x.db)


def quantities(a_interval, b_interval, logs):
    a = J.make(a_interval, da=1)
    b = J.make(b_interval, db=1)
    p = {}
    h = J.make(0)
    for n in range(1, 10):
        if n >= 2:
            p[n] = h/exp_jet(a*logs[n])
        if n < 9:
            h += exp_jet(b*logs[n]).reciprocal()
    mu = p[3]/(2*p[2])
    A = 4*p[3]*mu**2-4*p[4]*mu+p[5]
    Ap = 8*p[3]*mu-4*p[4]
    B = 8*p[4]*mu**3-12*p[5]*mu**2+6*p[6]*mu-p[7]
    Bp = 24*p[4]*mu**2-24*p[5]*mu+6*p[6]
    C = (16*p[5]*mu**4-32*p[6]*mu**3+24*p[7]*mu**2
         -8*p[8]*mu+p[9])
    K = -A/(2*p[2])
    Q = -(Ap*K+B)/(2*p[2])
    R = -(Ap*Q+4*p[3]*K**2+Bp*K+C)/(2*p[2])
    R0 = -C/(2*p[2])
    det = K.da*Q.db-K.db*Q.da
    return dict(mu=mu, K=K, Q=Q, R=R, R_at_KQ_zero=R0,
                determinant=det, q_prime=det/K.da,
                threshold_slope=-K.db/K.da)


def dec(x, places):
    scale = 10**places
    n = floor_f(x*scale)
    sign = '-' if n < 0 else ''
    n = abs(n)
    return f'{sign}{n//scale}.{n%scale:0{places}d}'


def serialize(x, places=66):
    scale = 10**places
    lo = F(floor_f(x.lo*scale), scale)
    hi = F(ceil_f(x.hi*scale), scale)
    return dict(lower=str(x.lo), upper=str(x.hi),
                decimal_lower=dec(lo, places), decimal_upper=dec(hi, places))


def main():
    logs = {n: log_integer(n) for n in range(1, 10)}
    b_lo = F('0.9974937898734204210746055930669')
    b_hi = F('0.9974937898734204210746055930670')
    a_lo = F('1.0014301809614951381293517293')
    a_hi = F('1.0014301809614951381293517295')
    a_box, b_box = I.make(a_lo, a_hi), I.make(b_lo, b_hi)
    endpoint_boxes = [
        (b_lo, F('1.001430180961495138129351729388732646668324449650396773411712'),
         F('1.001430180961495138129351729388732646668324449650396773411713')),
        (b_hi, F('1.001430180961495138129351729388675555307689905158335753809320'),
         F('1.001430180961495138129351729388675555307689905158335753809321')),
    ]
    entire = quantities(a_box, b_box, logs)
    assert entire['K'].da.hi < 0
    assert entire['K'].db.hi < 0
    assert entire['determinant'].hi < 0
    assert entire['q_prime'].lo > 0
    assert entire['R_at_KQ_zero'].v.hi < 0
    left_face = quantities(I.make(a_lo), b_box, logs)['K'].v
    right_face = quantities(I.make(a_hi), b_box, logs)['K'].v
    assert left_face.lo > 0
    assert right_face.hi < 0
    endpoints = []
    for index, (b, al, ah) in enumerate(endpoint_boxes):
        low = quantities(I.make(al), I.make(b), logs)
        high = quantities(I.make(ah), I.make(b), logs)
        box = quantities(I.make(al, ah), I.make(b), logs)
        assert low['K'].v.lo > 0
        assert high['K'].v.hi < 0
        q = box['Q'].v
        assert q.hi < 0 if index == 0 else q.lo > 0
        endpoints.append(dict(
            b=str(b), a_lower=str(al), a_upper=str(ah),
            K_at_lower=serialize(low['K'].v),
            K_at_upper=serialize(high['K'].v),
            Q_at_K_zero=serialize(q)))
    interval_values = {}
    for key, value in entire.items():
        if isinstance(value, J):
            interval_values[key] = dict(value=serialize(value.v),
                                       derivative_a=serialize(value.da),
                                       derivative_b=serialize(value.db))
        else:
            interval_values[key] = serialize(value)
    certificate = dict(
        status='PASS: all assertions proved with outward rational intervals',
        precision_bits=BITS, log_terms=LOG_TERMS, exp_terms=EXP_TERMS,
        outer_rectangle=dict(a_lower=str(a_lo), a_upper=str(a_hi),
                             b_lower=str(b_lo), b_upper=str(b_hi)),
        K_left_face=serialize(left_face), K_right_face=serialize(right_face),
        endpoint_certificates=endpoints,
        quantities_throughout_rectangle=interval_values,
        conclusion=[
            'There is a unique root of K=Q=0 in the outer rectangle.',
            'The root is the unique zero of Q(a_star(b),b) over its b interval.',
            'Its sextic radial coefficient R is strictly negative.',
            'The parameter map (a,b) -> (K,Q) has negative Jacobian determinant.',
            'Global uniqueness of the quartic transition for 0<b<1 is not proved.'
        ])
    path = Path(__file__).resolve().parents[1] / 'data' / 'double_turning_certificate.json'
    path.parent.mkdir(exist_ok=True)
    path.write_text(json.dumps(certificate, indent=2)+'\n')
    compact = dict(status=certificate['status'], output=str(path))
    for key in ['determinant', 'q_prime', 'threshold_slope']:
        v = entire[key]
        compact[key] = [serialize(v)['decimal_lower'], serialize(v)['decimal_upper']]
    v = entire['R_at_KQ_zero'].v
    compact['R_at_KQ_zero'] = [serialize(v)['decimal_lower'], serialize(v)['decimal_upper']]
    compact['Q_endpoint_signs'] = [
        [e['Q_at_K_zero']['decimal_lower'], e['Q_at_K_zero']['decimal_upper']]
        for e in endpoints]
    print(json.dumps(compact, indent=2))


if __name__ == '__main__':
    main()
