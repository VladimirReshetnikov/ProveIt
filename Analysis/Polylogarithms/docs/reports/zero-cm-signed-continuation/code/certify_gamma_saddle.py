#!/usr/bin/env python3
"""Exact rational certificate for reflected log-gamma saddle uniqueness.

Only Python's standard library is used.  No floating-point value enters an
inequality.  The central interval is covered by [j/256,(j+1)/256], 16<=j<128.
The two endpoints are handled analytically in the accompanying proof.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
from functools import lru_cache
import argparse
import json
from pathlib import Path


@dataclass(frozen=True)
class I:
    lo: Q
    hi: Q

    def __post_init__(self):
        assert self.lo <= self.hi

    def __add__(self, other):
        if not isinstance(other, I):
            other = I(Q(other), Q(other))
        return I(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __neg__(self):
        return I(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + (-other if isinstance(other, I) else -Q(other))

    def scale(self, c):
        c = Q(c)
        return I(c * self.lo, c * self.hi) if c >= 0 else I(c * self.hi, c * self.lo)


def log_1_to_2(x, terms=32):
    """log(x), 1<=x<=2, from 2*atanh((x-1)/(x+1))."""
    x = Q(x)
    assert 1 <= x <= 2
    y = (x - 1) / (x + 1)
    s = sum((2 * y ** (2 * k + 1) / (2 * k + 1)
             for k in range(terms)), Q(0))
    rem = 2 * y ** (2 * terms + 1) / ((2 * terms + 1) * (1 - y*y))
    return I(s, s + rem)


LOG2 = log_1_to_2(Q(2))


def log_q(x):
    x = Q(x)
    assert x > 0
    shift = 0
    while x < 1:
        x *= 2
        shift -= 1
    while x > 2:
        x /= 2
        shift += 1
    return log_1_to_2(x) + LOG2.scale(shift)


def euler_gamma():
    # 0 < gamma - (H_N-log N-1/(2N)) < 1/(12N^2).
    N = 32
    H = sum((Q(1, k) for k in range(1, N + 1)), Q(0))
    base = -log_q(Q(N)) + H - Q(1, 2*N)
    return I(base.lo, base.hi + Q(1, 12*N*N))


GAMMA = euler_gamma()
assert GAMMA.lo > Q(1, 2)
assert GAMMA.hi < Q(2, 3)
assert 4*LOG2.hi < 3
assert 3*(Q(1, 128)+Q(64, 225)) < 1


@lru_cache(None)
def zeta(k):
    assert k >= 2
    N = 32
    s = sum((Q(1, j**k) for j in range(1, N + 1)), Q(0))
    return I(s + Q(1, (k-1)*(N+1)**(k-1)),
             s + Q(1, (k-1)*N**(k-1)))


assert zeta(2).hi < 2


@lru_cache(None)
def functions(x, degree=40):
    """Return interval bounds for f,p,t,B,s,u.

    f=log Gamma(x), p=-psi(x), t=psi'(x),
    B=log Gamma(1-x), s=-psi(1-x), u=psi'(1-x).
    """
    x = Q(x)
    assert 0 < x <= Q(1, 2)
    f = -log_q(x) - GAMMA.scale(x)
    B = GAMMA.scale(x)
    p = GAMMA + 1/x
    s = GAMMA
    t = I(1/x**2, 1/x**2)
    u = I(Q(0), Q(0))
    for k in range(2, degree + 1):
        z = zeta(k)
        f = f + z.scale((-1)**k * x**k / k)
        B = B + z.scale(x**k / k)
        p = p + z.scale((-1)**(k+1) * x**(k-1))
        s = s + z.scale(x**(k-1))
        t = t + z.scale((-1)**k * (k-1) * x**(k-2))
        u = u + z.scale((k-1) * x**(k-2))
    ef = 2*x**(degree+1)/((degree+1)*(1-x))
    ep = 2*x**degree/(1-x)
    et = 2*x**(degree-1)*(Q(degree)/(1-x) + x/(1-x)**2)
    f = I(f.lo-ef, f.hi+ef)
    p = I(p.lo-ep, p.hi+ep)
    t = I(t.lo-et, t.hi+et)
    B = I(B.lo, B.hi+ef)
    s = I(s.lo, s.hi+ep)
    u = I(u.lo, u.hi+et)
    assert all(z.lo > 0 for z in (f, p, t, B, s, u))
    return f, p, t, B, s, u


def floor_rational(x, scale=10**9):
    """A short rational lower bound, still obtained entirely exactly."""
    return (x.numerator * scale // x.denominator), scale


def run(output_path=None):
    rows = []
    weakest = None
    for j in range(16, 128):
        a, b = Q(j, 256), Q(j+1, 256)
        fa, pa, ta, Ba, sa, ua = functions(a)
        fb, pb, tb, Bb, sb, ub = functions(b)
        # f,p,t decrease; B,s,u increase. Every denominator below is >0.
        lower = (pb.lo/fa.hi + sa.lo/Bb.hi
                 - ta.hi/pb.lo - ub.hi/sa.lo)
        assert lower > 0, (j, lower)
        short, scale = floor_rational(lower)
        assert Q(short, scale) <= lower
        rows.append({"j": j, "a": str(a), "b": str(b),
                     "D_lower_numerator": short, "D_lower_denominator": scale})
        if weakest is None or lower < weakest[1]:
            weakest = (j, lower)
    short, scale = floor_rational(weakest[1])
    report = {
        "statement": "d/dx log Q(x)>0 on [1/16,1/2]",
        "arithmetic": "exact fractions; no binary or decimal floating-point comparisons",
        "series_degree": 40,
        "log_atanh_terms": 32,
        "zeta_direct_terms": 32,
        "gamma_harmonic_N": 32,
        "intervals_checked": len(rows),
        "weakest_interval_j": weakest[0],
        "global_D_lower_numerator": short,
        "global_D_lower_denominator": scale,
        "rows": rows,
    }
    if output_path is not None:
        Path(output_path).write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps({k:v for k,v in report.items() if k != "rows"}, indent=2))
    return report


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true",
                        help="recompute all rational bounds and compare the stored certificate")
    args = parser.parse_args()
    target = (Path(__file__).resolve().parents[1] / "results" / "gamma_saddle_certificate.json")
    if args.check:
        expected = json.loads(target.read_text())
        assert run() == expected
        print("Stored certificate replayed successfully.")
    else:
        run(target)
