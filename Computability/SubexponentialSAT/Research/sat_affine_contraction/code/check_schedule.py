#!/usr/bin/env python3
"""Exact standard-library certificate for the 9,12,9,7,4-tail schedule.

Finite arithmetic validation only: the support lemmas and contraction identities
are mathematical inputs, not established by this checker.
"""
from __future__ import annotations
import argparse
import json
import math
from dataclasses import dataclass
from fractions import Fraction as F
from pathlib import Path


def require(test: bool, message: str) -> None:
    if not test:
        raise ValueError(message)


@dataclass(frozen=True)
class Interval:
    lo: F
    hi: F

    @classmethod
    def exact(cls, x):
        return cls(F(x), F(x))

    def __add__(self, other):
        other = promote(other)
        return Interval(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + (-promote(other))

    def __rsub__(self, other):
        return promote(other) - self

    def __mul__(self, other):
        other = promote(other)
        values = (self.lo * other.lo, self.lo * other.hi,
                  self.hi * other.lo, self.hi * other.hi)
        return Interval(min(values), max(values))

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = promote(other)
        require(other.lo > 0 or other.hi < 0, "Division interval contains zero")
        return self * Interval(1 / other.hi, 1 / other.lo)

    def __rtruediv__(self, other):
        return promote(other) / self


def promote(x):
    return x if isinstance(x, Interval) else Interval.exact(x)


def square_root(x) -> Interval:
    x = promote(x)
    require(x.lo >= 0, "Negative square-root input")
    scale = 1 << 180
    def lower(q):
        return F(math.isqrt(q.numerator * scale * scale // q.denominator), scale)
    return Interval(lower(x.lo), lower(x.hi) + F(1, scale))


def atan_reciprocal(q, n=100):
    total = sum((F((-1) ** k, (2 * k + 1) * q ** (2 * k + 1))
                 for k in range(n)), F(0))
    next_magnitude = F(1, (2 * n + 1) * q ** (2 * n + 1))
    return (Interval(total, total + next_magnitude) if n % 2 == 0
            else Interval(total - next_magnitude, total))


def constants():
    pi = 16 * atan_reciprocal(5) - 4 * atan_reciprocal(239)
    n = 160
    lower = 2 * sum((F(1, (2 * k + 1) * 3 ** (2 * k + 1))
                     for k in range(n)), F(0))
    remainder = 2 * F(1, (2 * n + 1) * 3 ** (2 * n + 1)) / (1 - F(1, 9))
    ln2 = Interval(lower, lower + remainder)
    return pi, ln2, pi * square_root(2) / ln2


def decimal_interval(x, digits=30):
    x = promote(x)
    scale = 10 ** digits
    a = (x.lo.numerator * scale) // x.lo.denominator
    b = -((-x.hi.numerator * scale) // x.hi.denominator)
    def fmt(t):
        sign = "-" if t < 0 else ""
        t = abs(t)
        return f"{sign}{t // scale}.{t % scale:0{digits}d}"
    return [fmt(a), fmt(b)]


def make_certificate():
    # u_d = floor(eta_d * (lambda - ceil(sqrt(lambda)))).
    r = [9, 12, 9, 7]
    eta = [F(1577, 100000), F(303, 25000), F(73, 20000), F(1, 250)]
    tail_r, q, total_capacity = 4, F(63, 100), F(1, 20)
    tail_budget = total_capacity - sum(eta)
    eta4 = (1 - q) * tail_budget
    require(tail_budget == F(723, 50000), "Tail budget")
    require(eta4 == F(26751, 5000000), "Initial geometric-tail taper")
    require(q > F(11, 20), "Minimum active taper must diverge")
    require(q > F(1, 4), "The paid tail must converge")

    log_upper = {9: F(317, 100), 12: F(717, 200), 7: F(281, 100), 4: F(2)}
    for base, exponent in log_upper.items():
        require(base ** exponent.denominator <= 2 ** exponent.numerator,
                f"Failed exact logarithm bound for {base}")
    A, gates = F(0), []
    for d, (rd, ud) in enumerate(zip(r, eta)):
        previous_A = A
        A += ud
        inherited = F(9, 10) + (2 if d == 0 else 1) * A * log_upper[rd]
        require(inherited < 1, f"Inherited-degree packing at depth {d}")
        fresh = None if d == 0 else 2 * A * log_upper[rd] + previous_A
        rounding = (1 + 2 * log_upper[rd]) * A
        if fresh is not None:
            require(fresh <= F(1, 4), f"Fresh-degree packing at depth {d}")
        require(rounding <= F(1, 4), f"Packet rounding at depth {d}")
        gates.append({"depth": d, "r": rd, "eta": str(ud),
                      "cumulative_eta": str(A), "inherited_exponent_upper": str(inherited),
                      "inherited_gap": str(1 - inherited),
                      "fresh_exponent_upper": None if fresh is None else str(fresh),
                      "rounding_exponent_upper": str(rounding)})
    require(F(9, 10) + 2 * total_capacity == 1, "Tail capacity boundary")
    require(5 * total_capacity == F(1, 4), "Tail fresh/rounding bound")

    pi, ln2, K = constants()
    masses = [F(1)]
    for rd in r:
        masses.append(masses[-1] * F(2, rd))
    require(masses == [F(1), F(2, 9), F(1, 27), F(2, 243), F(4, 1701)],
            "Child-size products")
    scales = [K * m / square_root(u) for m, u in zip(masses, eta + [eta4])]
    alpha = [square_root(2 * (rd - 1)) / rd for rd in r] + [square_root(6) / 4]
    beta2 = [F(1, 3), F(137, 400), F(1, 3), F(632, 1225), F(13, 25)]
    beta = [square_root(x) for x in beta2]
    prefix = Interval.exact(0)
    branches = []
    for d in range(4):
        branches.append(prefix + beta[d] * scales[d])
        prefix += alpha[d] * scales[d]
    gamma = 1 / (2 * square_root(q))
    require(gamma.hi < 1, "Divergent paid geometric tail")
    tail_multiplier = alpha[4] / (1 - gamma)
    require(tail_multiplier.lo > beta[4].hi, "Tail local work not covered by terminal route")
    tail_start = prefix + beta[4] * scales[4]
    terminal = prefix + tail_multiplier * scales[4]
    branches += [tail_start, terminal]
    time = branches[1]
    for d, value in enumerate(branches):
        if d != 1:
            require(value.hi < time.lo, f"Unexpected dominant branch {d}")
    require(time.hi < F(1513, 50), "Time coefficient is not below 30.26")

    # Root uses the joint time/space selector proved separately. Other stages
    # can use the more conservative guarantee storage <= local operation time.
    root_space_factor = square_root(F(7, 27))
    local_space = [root_space_factor * scales[0]]
    local_space += [beta[d] * scales[d] for d in range(1, 5)]
    space = local_space[0]
    for d, value in enumerate(local_space):
        if d:
            require(value.hi < space.lo, f"Unexpected dominant space stage {d}")
    require(space.hi < F(26), "Space coefficient is not below 26.00")

    # Deliberate false certificates exercise the numerical and gate checks.
    negative_controls = []
    for name, predicate in [
        ("time_below_30_25", time.hi < F(121, 4)),
        ("root_eta_16_1000", F(9, 10) + 2 * F(16, 1000) * log_upper[9] < 1),
        ("tail_ratio_1_2", F(1, 2) > F(11, 20)),
    ]:
        require(not predicate, f"Incorrect negative control accepted: {name}")
        negative_controls.append({"false_claim": name, "rejected": True})

    return {
        "status": "all exact finite checks passed",
        "scope": "Finite arithmetic certificate conditional on separately proved support and inherited contraction lemmas.",
        "alphabets": r + [tail_r],
        "taper_prefix": list(map(str, eta)),
        "taper_tail_first": str(eta4), "taper_tail_ratio": str(q),
        "tail_total_budget": str(tail_budget), "total_budget": str(total_capacity),
        "packet_rule": "a_d = sum_{j<=d} u_j + (d+1)*ceil(6 log2(lambda))",
        "taper_rule": "u_d = floor(eta_d*(lambda-ceil(sqrt(lambda))))",
        "leaf_rule": "M <= ceil(s/lambda)",
        "mass_coefficients": list(map(str, masses)),
        "alpha_squared": [str(F(2 * (rd - 1), rd * rd)) for rd in r + [tail_r]],
        "beta_squared": list(map(str, beta2)),
        "root_space_factor_squared": str(F(7, 27)),
        "packing_gates": gates,
        "tail_inherited_boundary": "1 - ceil(sqrt(lambda))/(10 lambda) + O((log lambda)^2/lambda)",
        "tail_fresh_and_rounding_exponent": "1/4 + o(1)",
        "gamma_interval": decimal_interval(gamma),
        "scale_intervals": list(map(decimal_interval, scales)),
        "branch_names": ["root", "depth_1", "depth_2", "depth_3", "tail_start", "terminal"],
        "branch_intervals": list(map(decimal_interval, branches)),
        "dominant_time_branch": "depth_1",
        "time_coefficient_interval": decimal_interval(time),
        "eventual_time_coefficient": "30.26",
        "local_space_intervals": list(map(decimal_interval, local_space)),
        "dominant_space_stage": "root",
        "space_coefficient_interval": decimal_interval(space),
        "eventual_space_coefficient": "26.00",
        "pi_interval": decimal_interval(pi), "ln2_interval": decimal_interval(ln2),
        "negative_controls": negative_controls,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", nargs="?", default="data/new_schedule.json")
    args = parser.parse_args()
    result = make_certificate()
    output = Path(args.output)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": result["status"], "time": result["time_coefficient_interval"],
                      "space": result["space_coefficient_interval"], "output": str(output)}))


if __name__ == "__main__":
    main()
