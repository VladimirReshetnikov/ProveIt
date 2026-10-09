#!/usr/bin/env python3
"""Exact finite checks for the signed block selection theorem.

Standard-library only. These checks do not prove the continuum-parameter
or probabilistic existence theorem; their purpose is to detect mistakes in
the state, passage, sign, index, separation, and grid claims used there.
"""

from fractions import Fraction as F
from itertools import combinations
from math import factorial
from pathlib import Path
import argparse
import json


CHECKS = {}


def check(category, condition, detail=""):
    CHECKS[category] = CHECKS.get(category, 0) + 1
    if not condition:
        raise AssertionError(f"{category}: {detail}")


def eye(n):
    return [[F(i == j) for j in range(n)] for i in range(n)]


def mm(a, b):
    return [[sum(x * y for x, y in zip(row, col))
             for col in zip(*b)] for row in a]


def mv(a, v):
    return [sum(x * y for x, y in zip(row, v)) for row in a]


def norm(a):
    return max(sum(map(abs, row)) for row in a)


def vnorm(v):
    return max(map(abs, v))


def det(a):
    if len(a) == 1:
        return a[0][0]
    return sum((-1) ** j * a[0][j] * det([
        row[:j] + row[j+1:] for row in a[1:]]) for j in range(len(a)))


def inv(a):
    n = len(a)
    b = [row[:] + e for row, e in zip(a, eye(n))]
    for j in range(n):
        pivot = next(i for i in range(j, n) if b[i][j])
        b[j], b[pivot] = b[pivot], b[j]
        scale = b[j][j]
        b[j] = [x / scale for x in b[j]]
        for i in range(n):
            if i != j:
                scale = b[i][j]
                b[i] = [x - scale * y for x, y in zip(b[i], b[j])]
    return [row[n:] for row in b]


def convolution(a, b):
    c = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i+j] += x * y
    return c


def companion(poly):
    check("polynomial_conventions", poly[-1] == 1)
    n = len(poly) - 1
    a = [[F(0)] * n for _ in range(n)]
    for i in range(n - 1):
        a[i][i+1] = F(1)
    a[-1] = [-x for x in poly[:-1]]
    return a


def ceil_fraction(x):
    return -((-x.numerator) // x.denominator)


def grid_n(c, q, b):
    target = c / q ** b
    n = 1
    while n < target:
        n *= 2
    check("dyadic_resolution", target <= n < 2 * target)
    return n


def key(n, x):
    return (x * n).__floor__() % n


def stable_constants(a):
    power = eye(len(a))
    for s in range(1, 1000):
        power = mm(power, a)
        if norm(power) < 1:
            break
    else:
        raise AssertionError("No stable power found in test example")
    actual = norm(power)
    L = max(2, ceil_fraction(norm(a)), ceil_fraction(1 / abs(det(a))),
            ceil_fraction(1 / (1 - actual)))
    rho = 1 - F(1, L)
    alpha = F(1, factorial(len(a)) * L ** len(a))
    check("matrix_box", norm(a) <= L)
    check("matrix_box", abs(det(a)) >= F(1, L))
    check("matrix_box", actual <= rho)
    check("inverse_bound", norm(inv(a)) <= 1 / alpha)
    return s, L, rho, alpha, actual


def exact_formula_checks():
    examples = [
        ([F(-1, 2), F(1)], lambda n: F(1, 2) ** n),
        ([F(2, 3), F(1)], lambda n: F(-2, 3) ** n),
        ([F(1, 4), F(0), F(1)],
         lambda n: F(0) if n % 2 else (-1) ** (n // 2) * F(1, 2) ** n),
        ([F(1, 16), F(0), F(1, 2), F(0), F(1)],
         lambda n: F(0) if n % 2 else
         (n + 1) * (-1) ** (n // 2) * F(1, 2) ** n),
    ]
    for polynomial, formula in examples:
        a = companion(polynomial)
        v = [formula(n) for n in range(len(a))]
        for n in range(90):
            check("closed_form_state", v[0] == formula(n))
            for i, value in enumerate(v):
                check("consecutive_block", value == formula(n+i))
            v = mv(a, v)


def sample_case(name, polynomial, raw_v, levels=12):
    a = companion(polynomial)
    m = len(a)
    s, L, rho, alpha_box, actual_power_norm = stable_constants(a)
    # A stronger exact inverse bound in this particular finite example keeps
    # the sample resolutions manageable. The general box bound is checked above.
    alpha = min(F(1, 2), 1 / (2 * norm(inv(a))))
    q = alpha / 8
    v0 = [F(x) / vnorm(raw_v) for x in raw_v]
    check("normalization", vnorm(v0) == 1)
    power = eye(m)
    for n in range(35):
        bound = rho ** (n // s) * L ** (s - 1)
        check("power_decay", norm(power) <= bound)
        power = mm(power, a)
    # Choose integer T0 so the exact power bound at every T0*j is <= q^j.
    # Use the sharper measured rational contraction for this fixed matrix;
    # the weaker uniform box bound has already been checked separately.
    decay = actual_power_norm
    C = norm(a) ** (s - 1) / decay
    T0 = 1
    while C * decay ** (T0 // s) > q:
        T0 += 1
    # The floor division is superadditive for integer multiples, so this
    # sufficient inequality proves the linear passage-index bound for every j.
    values = []
    norms = []
    states = []
    v = v0
    max_n = T0 * levels + m
    for n in range(max_n + 1):
        values.append(v[0])
        norms.append(vnorm(v))
        states.append(v)
        w = mv(a, v)
        check("lower_state_ratio", vnorm(w) >= alpha * vnorm(v))
        check("box_lower_state_ratio", vnorm(w) >= alpha_box * vnorm(v))
        check("nonzero_state", vnorm(v) > 0)
        v = w
    selected = []
    selected_indices = []
    passage = []
    for j in range(1, levels + 1):
        n = next(n for n in range(1, len(norms)) if norms[n] <= q ** j)
        i = next(i for i, x in enumerate(states[n]) if abs(x) == norms[n])
        scalar_index = n + i
        value = states[n][i]
        check("state_output_index", value == values[scalar_index])
        check("first_crossing", norms[n-1] > q ** j)
        check("signed_envelope", alpha * q ** j < abs(value) <= q ** j)
        check("linear_index_bound", n <= T0 * j)
        selected.append(value)
        selected_indices.append(scalar_index)
        passage.append({"j": j, "passage": n, "coordinate": i,
                        "original_index": scalar_index, "sign": 1 if value > 0 else -1})
    check("distinct_original_indices", len(set(selected_indices)) == levels)
    for j, k in combinations(range(levels), 2):
        check("signed_separation",
              abs(selected[j] - selected[k]) > (alpha - q) * q ** (j + 1))
    u, scale_max = F(1, 3), F(5)
    c = 4 / (u * (alpha - q))
    bprev = 1
    nprev = grid_n(c, q, bprev)
    start = bprev + 2
    while scale_max * q ** start >= F(1, 2 * nprev):
        start += 1
    end = start + 3
    check("enough_levels", end <= levels)
    center = F(1, 2 * nprev)
    check("signed_stability_margin",
          scale_max * q ** start < F(1, 2 * nprev))
    for t in [u, F(1), F(2), scale_max]:
        pts = [center] + [center + t * selected[j-1]
                          for j in range(start, end + 1)]
        for point in pts:
            check("signed_previous_key", key(nprev, point) == key(nprev, center))
        for b in [end, end + 1, end + 3]:
            ng = grid_n(c, q, b)
            check("distinct_refined_keys", len({key(ng, point) for point in pts}) == len(pts))
    # Negative controls: admitting a center on a boundary fails for negative
    # shifts, and using a zero state makes every first-crossing envelope fail.
    check("boundary_negative_control", key(nprev, -u * q ** start) != key(nprev, F(0)))
    zero = [F(0)] * m
    check("zero_state_negative_control", vnorm(mv(a, zero)) == 0)
    return {"name": name, "order": m, "stable_power": s, "L": L,
            "alpha": str(alpha), "alpha_box": str(alpha_box), "Q": str(q),
            "linear_bound_T": T0, "levels": levels,
            "initial_zero_terms": next((n for n, x in enumerate(values) if x), None),
            "zero_scalar_terms_checked": sum(x == 0 for x in values),
            "positive_selected": sum(x > 0 for x in selected),
            "negative_selected": sum(x < 0 for x in selected),
            "passages": passage}


def nilpotent_tail_check():
    # a=(7,-11,b_0,b_1,...) with b_n=(-1/2)^n. Its annihilator is
    # X^2(X+1/2); removing the zero roots gives the claimed stable tail.
    a = [F(7), F(-11)] + [F(-1, 2) ** n for n in range(65)]
    for n in range(len(a) - 3):
        check("zero_root_tail_reduction", a[n+3] + F(1, 2) * a[n+2] == 0)
    nilpotent = [[F(0), F(1)], [F(0), F(0)]]
    check("eventually_zero_excluded", det(nilpotent) == 0)
    check("eventually_zero_excluded", mv(nilpotent, mv(nilpotent, [F(1), F(1)])) == [0, 0])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", type=Path, default=Path(__file__).resolve().parent.parent / "verification" / "recurrences.json")
    args = parser.parse_args()
    exact_formula_checks()
    p_repeat_real = convolution(convolution([F(-1,2), F(1)],
                                           [F(-1,2), F(1)]), [F(1,3), F(1)])
    p_mixed = convolution(convolution([F(-1,2), F(1)], [F(1,3), F(1)]),
                          [F(-2,5), F(1)])
    cases = [
        ("positive_geometric", [F(-1,2), F(1)], [F(1)]),
        ("alternating_geometric", [F(2,3), F(1)], [F(1)]),
        ("oscillatory_exact_zeros", [F(1,4), F(0), F(1)], [F(1), F(0)]),
        ("complex_angle_pi_over_three", [F(1,4), F(-1,2), F(1)], [F(0), F(1)]),
        ("repeated_complex_roots", [F(1,16), F(0), F(1,2), F(0), F(1)],
         [F(1), F(0), F(-3,4), F(0)]),
        ("repeated_real_and_negative_root", p_repeat_real, [F(0), F(0), F(1)]),
        ("mixed_cancellation", p_mixed,
         [F(1,2)**n + F(-1,3)**n - 2 * F(2,5)**n for n in range(3)]),
    ]
    results = [sample_case(*case) for case in cases]
    nilpotent_tail_check()
    report = {"status": "passed", "arithmetic": "exact rational and integer",
              "scope": "finite state/selection/grid checks, not universal theorem verification",
              "checks": CHECKS, "total_checks": sum(CHECKS.values()), "cases": results}
    target = args.json
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": report["status"], "total_checks": report["total_checks"],
                      "cases": len(results), "output": target.name}, indent=2))


if __name__ == "__main__":
    main()
