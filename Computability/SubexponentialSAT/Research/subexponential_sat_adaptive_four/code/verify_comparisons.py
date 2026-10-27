#!/usr/bin/env python3
"""Exact interval audit of the prior composition and optional backend.

Uses the independent rational interval primitives in audit_global_schedule.
Floating point is used only for human-readable diagnostics, never decisions.
"""
import json
from fractions import Fraction as F
from audit_global_schedule import (
    point, add, sub, mul, div, sqrt_q, atan_inv, log_two,
    decimal_bounds, require_lt,
)


def run():
    pi = sub(mul(point(16), atan_inv(5)), mul(point(4), atan_inv(239)))
    ln2 = log_two()
    kappa = div(mul(pi, sqrt_q(2)), ln2)
    arities = (8, 12, 8, 4)
    fractions = (F(1,60), F(1,90), F(1,180), F(1,160))
    masses = (F(1), F(1,4), F(1,24), F(1,96))
    K = [div(mul(kappa, point(m)), sqrt_q(f))
         for m, f in zip(masses, fractions)]
    alpha = [div(sqrt_q(2*(r-1)), point(r)) for r in arities]
    gamma = sqrt_q(F(2,5))

    def recurrence(local):
        prefix = point(0)
        candidates = []
        for j in range(4):
            candidates.append(add(prefix, mul(local[j], K[j])))
            if j < 3:
                prefix = add(prefix, mul(alpha[j], K[j]))
        limit = add(prefix, div(mul(alpha[3], K[3]), sub(point(1), gamma)))
        return candidates, limit

    old_b8 = mul(point(F(3,32)), sqrt_q(56))
    old_b12 = sqrt_q(F(12,25))
    old_b4 = div(sqrt_q(F(208,25)), point(4))
    old, old_tail = recurrence((old_b8, old_b12, old_b8, old_b4))
    for x in old[1:] + [old_tail]:
        require_lt(x, old[0], "prior composite root maximum")
    old_space = mul(div(sqrt_q(30), point(8)), K[0])
    old_displayed_time = mul(div(pi, ln2), div(sqrt_q(24339), point(20)))
    old_displayed_space = mul(div(pi, ln2), div(sqrt_q(915), point(4)))
    require_lt(old[0], old_displayed_time, "composed prior strengthens displayed time")
    require_lt(old_space, old_displayed_space, "composed prior strengthens displayed space")

    variants = {}
    for omega in (F(12,5), F(19,8)):
        beta2 = (omega*omega+4)/24
        beta = sqrt_q(beta2)
        candidates, tail = recurrence((beta,)*4)
        for j in (0,2,3):
            require_lt(candidates[j], candidates[1], "new depth-one maximum")
        require_lt(tail, candidates[1], "new infinite tail maximum")
        require_lt(candidates[1], old[0], "new time below prior composition")
        require_lt(candidates[0], old_space, "new space below prior composition")
        require_lt(candidates[1], point(33), "safe eventual time coefficient")
        require_lt(candidates[0], point(32), "safe eventual space coefficient")

        # The weighted-entropy square uses 1,1,(omega-2) on the classes.
        discount = 1-(omega-2)**2
        pair2 = (26-2*discount)/64
        triple2 = (58-4*discount)/144
        if not (pair2 < beta2 and triple2 < beta2):
            raise ArithmeticError("initial table building must be charged")
        variants[str(omega)] = {
            "local_coefficient_squared": str(beta2),
            "time": decimal_bounds(candidates[1]),
            "space": decimal_bounds(candidates[0]),
            "all_time_candidates": [decimal_bounds(x) for x in candidates],
            "tail_limit": decimal_bounds(tail),
            "pair_build_squared": str(pair2),
            "triple_build_squared": str(triple2),
        }
    return {
        "status": "passed",
        "prior_composed_time": decimal_bounds(old[0]),
        "prior_composed_space": decimal_bounds(old_space),
        "prior_displayed_time": decimal_bounds(old_displayed_time),
        "prior_displayed_space": decimal_bounds(old_displayed_space),
        "prior_composed_candidates": [decimal_bounds(x) for x in old],
        "prior_composed_tail": decimal_bounds(old_tail),
        "new_variants": variants,
        "meaning": "Comparisons of proved upper-bound certificates, not runtime measurements.",
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
