"""Exact rational certificates for the new <38 time, <34 space schedule.

No floating-point value is used to decide an inequality.  Decimal displays
are supplemental.  The bound log2(7)<281/100 follows from an integer power
comparison; sqrt intervals use integer isqrt; pi and ln2 bounds are stated.
"""
from fractions import Fraction as F
from math import isqrt, gcd
from pathlib import Path
import json
import sys


SCALE = 10**15


def sqrt_interval(x):
    x = F(x)
    if x < 0:
        raise ValueError("negative square root")
    low = isqrt((x.numerator*SCALE*SCALE)//x.denominator)
    while F((low+1)**2, SCALE*SCALE) <= x:
        low += 1
    lo = F(low, SCALE)
    hi = lo if lo*lo == x else F(low+1, SCALE)
    if not lo*lo <= x <= hi*hi:
        raise ArithmeticError("invalid sqrt enclosure")
    return lo, hi


def sqrthi(x):
    return sqrt_interval(x)[1]


def sqrtlo(x):
    return sqrt_interval(x)[0]


def demand(value, message):
    if not value:
        raise ArithmeticError(message)


def packing_certificate(r, A, root=False):
    exponent = A*(20 if root else 10)
    base_power, two_power = exponent.numerator, exponent.denominator
    passed = pow(r, base_power) < pow(2, two_power)
    demand(passed, "packing exponent failed")
    return {"r": r, "cumulative_A": str(A), "base_exponent": base_power,
            "two_exponent": two_power, "inequality": f"{r}^{base_power} < 2^{two_power}",
            "verified": passed}


def factors(r):
    blocks = (r//3, (r+1)//3, (r+2)//3)
    pairs = [2*blocks[i]*blocks[j] for i, j in ((0, 1), (0, 2), (1, 2))]
    cache_sq = F(2*(r-1), r*r)
    build_sq = max(F(2*r*t-t*t-t, r*r) for t in blocks)
    store_sq = max(F(2*t*(r-t), r*r) for t in blocks)
    # This is an upper bound, since the expression increases with omega>2.
    omega_upper = F(281, 100)
    strassen_sq_upper = F(sum(pairs), r*r) - (1-(omega_upper-2)**2)*F(min(pairs), r*r)
    return cache_sq, build_sq, store_sq, strassen_sq_upper


def main():
    demand(7**100 < 2**281, "log2 7 upper bound failed")
    # ln2=2 sum_{j>=0} 3^(-2j-1)/(2j+1), all terms positive.
    log2_partial = sum((F(2, (2*j+1)*3**(2*j+1)) for j in range(4)), F(0))
    demand(log2_partial > F(6931, 10000), "ln2 lower bound failed")
    coefficient_upper = F(22, 7)*sqrthi(2)/F(6931, 10000)
    rs = [7, 9, 8, 6, 5, 4, 4]
    xs = [F(89, 5000), F(13, 1250), F(29, 10000)] + [F(1, 500)]*4
    root_time_lower = sqrtlo(F(30, 49)/xs[0])
    root_time_upper = sqrthi(F(30, 49)/xs[0])
    root_space_lower = sqrtlo(F(24, 49)/xs[0])
    root_space_upper = sqrthi(F(24, 49)/xs[0])
    A, m, prefix = F(0), F(1), F(0)
    records, packing = [], []
    for d, (r, x) in enumerate(zip(rs, xs)):
        A += x
        packing.append(packing_certificate(r, A, root=(d == 0)))
        ac, bb, jj, bs = factors(r)
        K_upper = m/sqrtlo(x)
        cost_upper = prefix + max(sqrthi(bb), sqrthi(bs))*K_upper
        memory_upper = sqrthi(jj)*K_upper
        if d:
            demand(cost_upper < root_time_lower, "root not proved to dominate time")
            demand(memory_upper < root_space_lower, "root not proved to dominate memory")
        else:
            demand(bs < bb, "root block-building does not dominate Strassen")
        records.append({"depth": d, "r": r, "x": str(x), "A": str(A), "mass": str(m),
                        "time_coefficient_rational_upper": str(coefficient_upper*cost_upper),
                        "time_coefficient_upper_display": float(coefficient_upper*cost_upper),
                        "memory_coefficient_upper_display": float(coefficient_upper*memory_upper),
                        "root_dominates": True})
        prefix += sqrthi(ac)*K_upper
        m *= F(2, r)
    demand(m == F(1, 1890), "tail mass mismatch")
    tail_x = (F(63, 1000)-A)/4
    demand(tail_x == F(239, 40000), "tail weight mismatch")
    packing.append(packing_certificate(3, F(63, 1000)))
    gamma_upper = F(4, 3)/sqrtlo(3)
    demand(gamma_upper < 1, "tail fails to decay")
    ac, bb, jj, bs = factors(3)
    K_upper = m/sqrtlo(tail_x)
    tail_time = prefix + K_upper*max(max(sqrthi(bb), sqrthi(bs)), sqrthi(ac)/(1-gamma_upper))
    tail_space = sqrthi(jj)*K_upper
    demand(tail_time < root_time_lower, "root does not dominate complete tail")
    demand(tail_space < root_space_lower, "root does not dominate tail memory")
    demand(coefficient_upper*root_time_upper < 38, "time <38 not certified")
    demand(coefficient_upper*root_space_upper < 34, "space <34 not certified")
    result = {
        "status": "PASS", "inequalities_use": "integer arithmetic and exact Fractions only",
        "pi_bound": "pi < 22/7", "ln2_bound": "ln2 > 6931/10000, certified by four positive series terms",
        "omega_bound": "log2(7) < 281/100, certified by 7^100 < 2^281",
        "time_exact_expression": "(pi*sqrt(2)/ln(2))*sqrt(30)/(7*sqrt(89/5000))",
        "space_exact_expression": "(pi*sqrt(2)/ln(2))*sqrt(24)/(7*sqrt(89/5000))",
        "time_rational_upper": str(coefficient_upper*root_time_upper),
        "space_rational_upper": str(coefficient_upper*root_space_upper),
        "time_upper_display": float(coefficient_upper*root_time_upper),
        "space_upper_display": float(coefficient_upper*root_space_upper),
        "prefix": records, "packing_certificates": packing,
        "tail": {"mass": str(m), "first_x": str(tail_x), "x_ratio": "3/4",
                 "time_upper_display": float(coefficient_upper*tail_time),
                 "root_dominates": True},
        "scope": "New explicit cached-table schedule under inherited tensor contraction identities; not end-to-end formal verification."
    }
    destination = Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parents[1] / "results" / "cache_schedule_checks.json"
    destination.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
