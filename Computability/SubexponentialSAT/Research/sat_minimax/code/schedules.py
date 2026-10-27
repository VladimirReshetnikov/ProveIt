#!/usr/bin/env python3
"""Exact rational interval checks for paid contraction schedules.

No binary floating point participates in validation. Logarithms, pi and square
roots are enclosed using convergent series and integer square roots.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
import json

from adaptive_rectangular import data, supports, dot, require


def I(x):
    x = F(x)
    return x, x


def add(a, b):
    return a[0] + b[0], a[1] + b[1]


def sub(a, b):
    return a[0] - b[1], a[1] - b[0]


def mul(a, b):
    values = [x*y for x in a for y in b]
    return min(values), max(values)


def div(a, b):
    require(b[0] > 0, "Positive divisor required")
    return mul(a, (1/b[1], 1/b[0]))


def sqrt_point(x):
    require(x >= 0, "Negative square root")
    scale = 10**55
    k = isqrt((x.numerator * scale**2) // x.denominator)
    lo = F(k, scale)
    hi = lo if k*k*x.denominator == x.numerator*scale**2 else F(k+1, scale)
    return lo, hi


def sqrt(a):
    return sqrt_point(a[0])[0], sqrt_point(a[1])[1]


def atanh_log(x):
    """ln(x) for 1 <= x <= 2, using 100 nonnegative terms."""
    require(1 <= x <= 2, "Log argument outside reduced interval")
    z = (x - 1) / (x + 1)
    power = z
    total = F(0)
    for j in range(100):
        total += 2 * power / (2*j + 1)
        power *= z*z
    remainder = 2*power / (201*(1-z*z))
    return total, total + remainder


LN2 = atanh_log(F(2))


def log2_integer(n):
    k = n.bit_length() - 1
    return add(I(k), div(atanh_log(F(n, 2**k)), LN2))


def atan(x):
    total = F(0)
    power = x
    for j in range(100):
        total += (-1 if j % 2 else 1) * power / (2*j + 1)
        power *= x*x
    # 100 terms end with a negative term; next term is positive.
    return total, total + power/201


PI = sub(mul(I(16), atan(F(1, 5))), mul(I(4), atan(F(1, 239))))
KAPPA = div(mul(PI, sqrt(I(2))), LN2)


def decimal_floor(x, digits=45):
    scale = 10**digits
    v = (x.numerator * scale) // x.denominator
    sign = "-" if v < 0 else ""
    v = abs(v)
    return sign + str(v // scale) + "." + str(v % scale).zfill(digits)


def display(a):
    # Positive coefficients and margins only.
    require(a[0] >= 0, "Display expects nonnegative interval")
    scale = F(1, 10**45)
    return {"lower": decimal_floor(a[0]), "upper": decimal_floor(a[1] + scale)}


def fixed_beta2(r, backend):
    first = (r + 2) // 3
    second = (r - first + 1) // 2
    plan = [list(range(first)), list(range(first, first+second)),
            list(range(first+second, r))]
    maximum = max(dot(v, v) for v in supports(r, plan, backend))
    return F(2*maximum, backend["denominator"]**2 * r*r)


def bound_schedule(rs, etas, tail_r, tail_first, tail_q, beta2, epsilon):
    etas = list(map(F, etas))
    tail_first, tail_q = F(tail_first), F(tail_q)
    require(len(rs) == len(etas), "Mismatched prefix lengths")
    require(tail_q > F(2, tail_r), "Tail taper does not close depth bootstrap")
    depth_ratio = (tail_q + F(2, tail_r)) / 2
    require(F(2, tail_r) < depth_ratio < tail_q < 1,
            "Invalid strict depth-bootstrap ratio")
    A = F(0)
    gates = []
    for depth, (r, eta) in enumerate(zip(rs, etas)):
        previous = A
        A += eta
        log_r = log2_integer(r)
        old = add(I(F(9, 10)), mul(I((2 if depth == 0 else 1)*A), log_r))
        require(old[1] < 1, "Old-side packing gate failed")
        rounding = mul(I(A), add(mul(I(2), log_r), I(1)))
        require(rounding[1] < 1, "Packet-rounding gate failed")
        row = {"depth": depth, "r": r, "eta": str(eta), "cumulative": str(A),
               "old_side_gap": display(sub(I(1), old)),
               "rounding_gap": display(sub(I(1), rounding))}
        if depth:
            fresh = add(mul(I(2*A), log_r), I(previous))
            require(fresh[1] < 1, "Fresh-side packing gate failed")
            row["fresh_side_gap"] = display(sub(I(1), fresh))
        gates.append(row)
    Ainf = A + tail_first/(1-tail_q)
    tail_log = log2_integer(tail_r)
    tail_old = add(I(F(9, 10)), mul(I(Ainf), tail_log))
    tail_other = mul(I(Ainf), add(mul(I(2), tail_log), I(1)))
    require(tail_old[1] < 1 and tail_other[1] < 1, "Tail packing failed")
    require(Ainf < F(9, 10), "Fresh degree exceeds original root cap")

    prefix_cost = I(0)
    mass = F(1)
    times, spaces = [], []
    for r, eta in zip(rs, etas):
        K = div(mul(KAPPA, I(mass)), sqrt(I(eta)))
        alpha = sqrt(I(F(2*(r-1), r*r)))
        beta = sqrt(I(beta2[r]))
        local = mul(beta, K)
        times.append(add(prefix_cost, mul(I(1+epsilon), local)))
        spaces.append(local)
        prefix_cost = add(prefix_cost, mul(alpha, K))
        mass *= F(2, r)
    Ktail = div(mul(KAPPA, I(mass)), sqrt(I(tail_first)))
    gamma = div(I(F(2, tail_r)), sqrt(I(tail_q)))
    alpha = sqrt(I(F(2*(tail_r-1), tail_r*tail_r)))
    local = mul(I(1+epsilon), sqrt(I(beta2[tail_r])))
    infinite = div(alpha, sub(I(1), gamma))
    maximum = (max(local[0], infinite[0]), max(local[1], infinite[1]))
    times.append(add(prefix_cost, mul(Ktail, maximum)))
    spaces.append(mul(Ktail, sqrt(I(beta2[tail_r]))))
    Tmax = (max(x[0] for x in times), max(x[1] for x in times))
    Smax = (max(x[0] for x in spaces), max(x[1] for x in spaces))
    return {
        "r_prefix": rs, "eta_prefix": [str(x) for x in etas],
        "tail_r": tail_r, "tail_first": str(tail_first), "tail_ratio": str(tail_q),
        "eventual_child_ratio_for_depth_bootstrap": str(depth_ratio),
        "cumulative_limit": str(Ainf), "packing": gates,
        "tail_old_side_gap": display(sub(I(1), tail_old)),
        "tail_other_gap": display(sub(I(1), tail_other)),
        "time_branches": [display(x) for x in times],
        "space_branches": [display(x) for x in spaces],
        "time": display(Tmax), "space": display(Smax),
    }, Tmax, Smax


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    payload = data()
    answer = {"status": "PASS", "schedules": {}}
    for name, config in payload["schedules"].items():
        backend = payload["backends"][name]
        beta2 = {r: fixed_beta2(r, backend) for r in (3, 4, 5, 6, 8)}
        for entry in payload["certificates"]:
            if entry["backend"] == name:
                beta2[entry["r"]] = F(entry["beta_squared"])
        record, T, S = bound_schedule(
            config["prefix_r"], config["prefix_eta"], config["tail_r"],
            config["tail_first"], config["tail_ratio"], beta2, F(backend["epsilon"]))
        require(T[1] < F(config["safe_time"]), "Eventual time certificate failed")
        require(S[1] < F(config["safe_space"]), "Eventual space certificate failed")
        record["beta_squared"] = {str(r): str(b) for r, b in sorted(beta2.items())}
        record["safe_eventual_time"] = config["safe_time"]
        record["safe_eventual_space"] = config["safe_space"]
        answer["schedules"][name] = record
    encoded = json.dumps(answer, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(encoded)
    print(encoded, end="")


if __name__ == "__main__":
    main()
