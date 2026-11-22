#!/usr/bin/env python3
"""Exact finite continuous-formula evaluation and an alternating minimax example.

Reference computation for sections M2--M6 of the report.  This is an executable
illustration, not an iPRA proof checker.  Quantifiers range over finite lists;
terms in atoms are evaluated in the ambient rational domain.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction as Q
import json
from pathlib import Path
from typing import Callable, Mapping, Sequence


@dataclass(frozen=True)
class Formula:
    tag: str
    args: tuple = ()


def evaluate(formula: Formula, domain: Sequence[Q], env: Mapping[str, Q],
             atoms: Mapping[str, Callable[[Mapping[str, Q]], Q]]) -> Q:
    """Evaluate the fixed finite syntax using exact rational min/max semantics."""
    if not domain:
        raise ValueError("The metric sort must be inhabited")
    tag, args = formula.tag, formula.args
    if tag == "atom":
        return atoms[args[0]](env)
    if tag == "constant":
        return Q(args[0])
    if tag == "complement":
        return 1 - evaluate(args[0], domain, env, atoms)
    if tag in ("min", "max"):
        values = [evaluate(child, domain, env, atoms) for child in args]
        return (min if tag == "min" else max)(values)
    if tag in ("inf", "sup"):
        variable, child = args
        values = [evaluate(child, domain, dict(env, **{variable: x}), atoms)
                  for x in domain]
        return (min if tag == "inf" else max)(values)
    raise ValueError(f"Unknown constructor: {tag}")


MINIMAX = Formula("inf", ("c", Formula("sup", ("x", Formula("atom", ("loss",))))))
ATOMS = {"loss": lambda e: abs(e["x"] ** 2 - e["c"] * e["x"])}


def dyadic_net(level: int) -> list[Q]:
    if level < 0:
        raise ValueError("level must be nonnegative")
    n = 1 << level
    return [Q(j, n) for j in range(n + 1)]


def finite_minimax(level: int) -> tuple[Q, Q]:
    """Exact evaluation after the proved one-variable quadratic maximum reduction.

    For c=i/N the largest |x*x-c*x| on x=j/N is
        max(N*(N-i), floor(i*i/4))/N**2.
    Its positive maximum is at j=N; its negative maximum is attained at one of
    the integers adjacent to i/2.  Only the outer finite minimum remains.
    """
    if level < 0:
        raise ValueError("level must be nonnegative")
    n = 1 << level
    best_value, best_index = None, None
    for i in range(n + 1):
        loss = max(n * (n - i), (i * i) // 4)
        if best_value is None or loss < best_value:
            best_value, best_index = loss, i
    return Q(best_value, n * n), Q(best_index, n)


def square_root_two_bracket(bits: int = 100) -> tuple[Q, Q]:
    """Rational bisection bracket, verified by exact squaring at every step."""
    lo, hi = Q(1), Q(2)
    for _ in range(bits):
        mid = (lo + hi) / 2
        if mid * mid <= 2:
            lo = mid
        else:
            hi = mid
    assert lo * lo <= 2 <= hi * hi
    return lo, hi


def run_checks() -> dict:
    # An independent full syntax/quantifier evaluation checks the algebraic
    # reduction on six meshes, rather than just replaying the reduced routine.
    direct_comparisons = []
    for level in range(6):
        full = evaluate(MINIMAX, dyadic_net(level), {}, ATOMS)
        reduced, _ = finite_minimax(level)
        assert full == reduced
        direct_comparisons.append({"level": level, "exact_value": str(full)})

    lo_sqrt, hi_sqrt = square_root_two_bracket()
    lo_value, hi_value = 3 - 2 * hi_sqrt, 3 - 2 * lo_sqrt
    lo_center, hi_center = 2 * lo_sqrt - 2, 2 * hi_sqrt - 2
    rows = []
    previous = None
    for level in (2, 4, 6, 8, 10, 12, 14, 16):
        value, center = finite_minimax(level)
        error = Q(4, 1 << level)
        # This compares the finite computation against a rational enclosure of
        # the independently proved analytic value 3 - 2 sqrt(2).
        assert value - error <= lo_value <= hi_value <= value + error
        center_error = Q(32, 1 << level)
        assert center - center_error <= lo_center <= hi_center <= center + center_error
        if previous is not None:
            old_level, old_value = previous
            assert abs(value - old_value) <= Q(4, 1 << old_level)
        rows.append({"level": level, "net_cardinality": (1 << level) + 1,
                     "value": str(value), "value_decimal": float(value),
                     "center": str(center), "center_decimal": float(center),
                     "proved_optimizer_error_bound": str(center_error),
                     "proved_generic_error_bound": str(error)})
        previous = level, value
    return {"status": "passed", "interpretation": "finite exact examples, not a proof checker",
            "sentence": "inf_c sup_x abs(x*x - c*x), c,x in [0,1]",
            "semantic_value": "3 - 2 sqrt(2)",
            "direct_evaluator_comparisons": direct_comparisons,
            "rational_enclosure_of_semantic_value": [str(lo_value), str(hi_value)],
            "refinements": rows}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = run_checks()
    data = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(data)
    print(data, end="")
