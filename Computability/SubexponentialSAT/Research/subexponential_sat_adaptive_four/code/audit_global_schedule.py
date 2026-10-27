#!/usr/bin/env python3
"""Independent exact-interval audit of the 8,12,8,4,... cached schedule.

This validates scalar algebra, capacity inequalities, and dominance of
all infinite-tail recurrence terms. It is not a SAT solver or formal proof.
"""
from fractions import Fraction as F
from math import isqrt
import json


def point(q):
    q = F(q)
    return q, q


def add(a, b):
    return a[0] + b[0], a[1] + b[1]


def sub(a, b):
    return a[0] - b[1], a[1] - b[0]


def mul(a, b):
    v = [x * y for x in a for y in b]
    return min(v), max(v)


def div(a, b):
    if b[0] <= 0 <= b[1]:
        raise ArithmeticError("interval division through zero")
    return mul(a, (1 / b[1], 1 / b[0]))


def sqrt_q(q):
    q = F(q)
    if q < 0:
        raise ValueError("negative square root")
    scale = 10**30
    lower_num = isqrt(q.numerator * scale**2 // q.denominator)
    lower, upper = F(lower_num, scale), F(lower_num + 1, scale)
    if not lower**2 <= q <= upper**2:
        raise ArithmeticError("bad square root enclosure")
    return lower, upper


def atan_inv(n, terms=80):
    total = sum((F((-1)**k, (2*k + 1)*n**(2*k + 1))
                 for k in range(terms)), F(0))
    nxt = F((-1)**terms, (2*terms + 1)*n**(2*terms + 1))
    return min(total, total + nxt), max(total, total + nxt)


def log_two(terms=100):
    total = 2 * sum((F(1, (2*k + 1)*3**(2*k + 1))
                     for k in range(terms)), F(0))
    tail = F(2, (2*terms + 1)*3**(2*terms + 1)) * F(9, 8)
    return total, total + tail


def decimal_bounds(a, digits=20):
    scale = 10**digits
    lo = a[0].numerator * scale // a[0].denominator
    hi = -((-a[1].numerator * scale) // a[1].denominator)
    def fmt(n):
        return f"{n // scale}.{n % scale:0{digits}d}"
    return [fmt(lo), fmt(hi)]


def require_lt(a, b, why):
    if not a[1] < b[0]:
        raise ArithmeticError(why)


def run():
    pi = sub(mul(point(16), atan_inv(5)), mul(point(4), atan_inv(239)))
    ln2 = log_two()
    kappa = div(mul(pi, sqrt_q(2)), ln2)
    b = sqrt_q(F(61, 150))
    f = (F(1,60), F(1,90), F(1,180), F(1,160))
    m = (F(1), F(1,4), F(1,24), F(1,96))
    r = (8,12,8,4)
    K = [div(mul(kappa, point(md)), sqrt_q(fd)) for fd,md in zip(f,m)]
    alpha = [div(sqrt_q(2*(rd-1)), point(rd)) for rd in r]
    gamma = sqrt_q(F(2,5))
    require_lt(gamma, point(1), "tail work must decrease")

    prefix = point(0)
    candidates = []
    for j in range(4):
        candidates.append(add(prefix, mul(b,K[j])))
        if j < 3:
            prefix = add(prefix,mul(alpha[j],K[j]))
    tail_limit = add(prefix, div(mul(alpha[3],K[3]), sub(point(1),gamma)))
    tail_multiplier = div(alpha[3],sub(point(1),gamma))
    require_lt(b,tail_multiplier,"tail candidates should increase to their limit")
    for j in (0,2,3):
        require_lt(candidates[j], candidates[1], f"depth {j} beats claimed time maximum")
    require_lt(tail_limit,candidates[1],"infinite tail beats claimed time maximum")

    time_closed = mul(div(pi,ln2),add(div(sqrt_q(105),point(2)),sqrt_q(F(183,40))))
    memory_closed = mul(div(pi,ln2),sqrt_q(F(244,5)))
    if max(time_closed[0],candidates[1][0]) > min(time_closed[1],candidates[1][1]):
        raise ArithmeticError("time closed form does not overlap recurrence value")
    if max(memory_closed[0],candidates[0][0]) > min(memory_closed[1],candidates[0][1]):
        raise ArithmeticError("memory closed form does not overlap recurrence value")

    pair_build = div(sqrt_q(F(608,25)),point(8))
    triple_build = div(sqrt_q(F(1366,25)),point(12))
    require_lt(pair_build,b,"r=8 pair-table formation exceeds adaptive bound")
    require_lt(triple_build,b,"r=12 triple-table formation exceeds adaptive bound")
    for j in range(4):
        require_lt(alpha[j],b,"group cache storage exceeds local bound")
    for j in range(1,4):
        require_lt(K[j],K[j-1],"level sizes must decrease for space maximum")

    A0=f[0]
    A1=sum(f[:2])
    A2=sum(f[:3])
    Ainf=A2+f[3]/(1-F(5,8))
    if (A0,A1,A2,Ainf)!=(F(1,60),F(1,36),F(1,30),F(1,20)):
        raise ArithmeticError("incorrect accumulated capacity")
    # Root and equality-boundary high-degree gates, before sqrt(lambda) reserve.
    if 2*3*A0 != F(1,10) or 3*A2 != F(1,10) or 2*Ainf != F(1,10):
        raise ArithmeticError("boundary capacities incorrect")
    if not 12**5 < 2**18:
        raise ArithmeticError("r=12 strict high-degree certificate failed")
    # Retained-range decay 5/8 is slower than eventual child decay 11/20.
    if not F(11,20)<F(5,8)<1:
        raise ArithmeticError("minimum retained range bootstrap failed")

    return {
        "status":"passed",
        "arithmetic":"rational intervals with integer-square-root and series enclosures",
        "K_values": [decimal_bounds(x) for x in K],
        "candidate_depth_values": [decimal_bounds(x) for x in candidates],
        "infinite_tail_value": decimal_bounds(tail_limit),
        "time_constant":decimal_bounds(time_closed),
        "space_constant":decimal_bounds(memory_closed),
        "local_b":decimal_bounds(b),
        "tail_ratio":decimal_bounds(gamma),
        "pair_table_factor_r8":decimal_bounds(pair_build),
        "triple_table_factor_r12":decimal_bounds(triple_build),
        "capacities":list(map(str,(A0,A1,A2,Ainf))),
        "r12_capacity_certificate":"12^5 < 2^18",
        "scope":"scalar schedule and recurrence audit; proof obligations are in accompanying note"
    }


if __name__=="__main__":
    print(json.dumps(run(),indent=2))
