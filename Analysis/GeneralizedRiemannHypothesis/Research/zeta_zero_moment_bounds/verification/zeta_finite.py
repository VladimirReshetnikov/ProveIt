"""Rational check of a finite zeta enclosure by order-3/4 deflation.

The four input intervals for M_j = sum (200/(1/4 + gamma^2))^j,
over positive ordinates with multiplicity, are outward roundings of
ProveIt's li_ritz_zero_recovery.zip, verification/certified_moments.json.
Git revision 244c77760d4dd675372c5bda2438c135e2fc802d. The source
generator verification/certify_moments.py regenerated the exact same
file, SHA256 b672abe6c0855beb5f69bfb4d25564b972a17e2629ef2b568a6a9f338526b407.
To also verify the roundings, give the generated JSON as the sole argument.
Run with Python 3 and assertions enabled. All arithmetic below is rational.
"""
from fractions import Fraction as F
from dataclasses import dataclass
import json
import sys


@dataclass(frozen=True)
class I:
    lo: F
    hi: F

    def __add__(self, other):
        return I(self.lo + other.lo, self.hi + other.hi)

    def __mul__(self, other):
        products = [a*b for a in (self.lo, self.hi) for b in (other.lo, other.hi)]
        return I(min(products), max(products))


def exact(x):
    return I(F(x), F(x))


def eval_at(cs, x):
    value = exact(0)
    for c in reversed(cs):
        value = value*x + c
    return value


def run():
    if not __debug__:
        raise RuntimeError("Run this checker with Python assertions enabled.")
    digits = [105572466326784184430480813, 100025018857591281580900012,
              99765036478443525027857289, 99677225165408692087482695]
    p = [None] + [I(F(v,10**26),F(v+1,10**26)) for v in digits]
    if len(sys.argv) > 1:
        with open(sys.argv[1], encoding="utf8") as f:
            rows = json.load(f)["moments"]
        for i in range(1,5):
            row = rows[4*i-1]
            assert row["k"] == 4*i
            assert p[i].lo <= F(row["lower"]) <= F(row["upper"]) <= p[i].hi
    # Largest powered mass A has Q/S <= A <= S; r <= S^2/Q < 2.
    assert p[1].hi**2 < 2*p[2].lo
    hull = I(F(94,100), F(118,100))
    assert hull.lo <= p[2].lo/p[1].hi <= p[1].hi <= hull.hi
    e = [exact(1)]
    for d in range(1,5):
        s = exact(0)
        for i in range(1,d+1):
            s = s + exact((-1)**(i-1))*e[d-i]*p[i]
        e.append(s * exact(F(1,d)))
    ordinates = {3: F('14.13472107'), 4: F('14.13472515')}
    # Bracket the relevant roots of P_d and of the respective tail polynomial.
    root_boxes = {3: ('0.999193608630','0.999193608633'),
                  4: ('0.999191309425','0.999191309428')}
    tail_boxes = {3: ((16,17),(39,40)), 4: ((5,6),(8,9),(41,42))}
    for d in (3,4):
        cs = [exact((-1)**j)*e[d-j] for j in range(d+1)]
        derivative = [exact(j)*cs[j] for j in range(1,d+1)]
        sign = (-1)**d
        g = ordinates[d]
        trial = (200/(g*g+F(1,4)))**4
        assert hull.lo < trial < hull.hi
        # The subdivision makes the interval-Horner derivative bound sharp.
        for j in range(16):
            width = (hull.hi-hull.lo)/16
            x = I(hull.lo+j*width, hull.lo+(j+1)*width)
            assert (exact(sign)*eval_at(derivative, x)).lo > 0
        assert eval_at(cs, exact(trial)).hi < 0
        box = I(*map(F,root_boxes[d]))
        assert hull.lo < box.lo < box.hi < hull.hi
        assert box.hi < p[1].lo
        # Every point closer to c=S than the indicated root lies in hull.
        radius = p[1].hi - box.lo
        assert hull.lo < p[1].lo - radius and p[1].hi + radius < hull.hi
        assert (exact(sign)*eval_at(cs,exact(box.lo))).hi < 0
        assert (exact(sign)*eval_at(cs,exact(box.hi))).lo > 0
        # At t = root, B_d(t)=0. Get B_0,...,B_{d-1} by formal division
        # by 1+t*u, then prove the reversed alternating polynomial has d-1
        # real positive roots strictly below t. Each lies in its own box.
        tail = [exact(1)]
        for j in range(1,d):
            tail.append(e[j] + exact(-1)*box*tail[j-1])
        poly = [exact((-1)**j)*bj for j,bj in enumerate(tail)][::-1]
        for m, (u,v) in enumerate(tail_boxes[d]):
            lo, hi = F(u,1000), F(v,1000)
            assert 0 < lo < hi < box.lo
            orientation = exact((-1)**(d-1-m))
            assert (orientation*eval_at(poly,exact(lo))).lo > 0
            assert (orientation*eval_at(poly,exact(hi))).hi < 0
        # P_d(A)>=0 by removing the largest mass. At d=3 P decreases, so
        # A<trial. At d=4 P increases, so A>trial. Invert to heights.
    print("Certified top multiplicity 1.")
    print("14.13472107 < first positive zeta ordinate < 14.13472515")
    print("Extremal branches attained at orders 3 and 4, with simple positive tails.")
    print("Used moments M_4, M_8, M_12, M_16 only.")


if __name__ == "__main__":
    run()
