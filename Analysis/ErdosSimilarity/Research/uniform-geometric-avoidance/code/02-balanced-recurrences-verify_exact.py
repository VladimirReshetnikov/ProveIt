#!/usr/bin/env python3
"""Exact finite corroboration for universal avoidance of recurrence patterns.

Python 3.10+; standard library only. This does not construct the universal
avoiding set, prove an infinite theorem, or provide a feasible QE algorithm.
It checks independently specified sequences, signed block sampling, rational
sign clearing, preorder spans, and an exhaustive finite routing probability.

Run:
    python3 code/verify_exact.py --output data/verification_results.json
"""
from __future__ import annotations

import argparse
import itertools
import json
import math
from dataclasses import dataclass
from fractions import Fraction as F
from pathlib import Path


def need(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def sign(x: F) -> int:
    return (x > 0) - (x < 0)


def evaluate(coefficients: tuple[F, ...], n: int) -> F:
    answer = F(0)
    for coefficient in reversed(coefficients):
        answer = answer * n + coefficient
    return answer


@dataclass(frozen=True)
class Example:
    name: str
    polynomials: tuple[tuple[F, ...], ...]  # A_0,...,A_d, ascending powers
    initial: tuple[F, ...]
    parameter_bound: int
    envelope_base: F
    scale: F

    @property
    def order(self) -> int:
        return len(self.initial)

    @property
    def alpha(self) -> F:
        r, d = self.parameter_bound, self.order
        return F(1, r * (1 + (d - 1) * r))


def scalar_recurrence(example: Example, count: int) -> list[F]:
    """Direct scalar recursion, separate from the matrix-product representation."""
    values = list(example.initial)
    d = example.order
    while len(values) < count:
        n = len(values) - d
        denominator = evaluate(example.polynomials[d], n)
        need(denominator != 0, "nonzero leading recurrence coefficient")
        numerator = sum(
            (evaluate(example.polynomials[j], n) * values[n + j]
             for j in range(d)), F(0)
        )
        values.append(-numerator / denominator)
    return values


def matrix_numerators(example: Example, count: int) -> tuple[list[F], list[F]]:
    """Use C(n)=A_d(n) M(n), recording P_n,D_n without rational cancellation."""
    d = example.order
    state = list(example.initial)
    denominator = F(1)
    numerators, denominators = [], []
    for n in range(count):
        numerators.append(state[0])
        denominators.append(denominator)
        ad = evaluate(example.polynomials[d], n)
        state = [ad * state[j + 1] for j in range(d - 1)] + [
            -sum((evaluate(example.polynomials[j], n) * state[j]
                  for j in range(d)), F(0))
        ]
        denominator *= ad
    return numerators, denominators


def complex_power(real: F, imag: F, exponent: int) -> tuple[F, F]:
    x, y = F(1), F(0)
    for _ in range(exponent):
        x, y = x * real - y * imag, x * imag + y * real
    return x, y


def rising(start: F, length: int) -> F:
    result = F(1)
    for k in range(length):
        result *= start + k
    return result


def legendre_coefficient_formula(n: int, x: F) -> F:
    """Independent explicit coefficient formula, not the three-term recurrence."""
    result = F(0)
    for k in range(n // 2 + 1):
        coefficient = F(
            (-1) ** k * math.factorial(2 * n - 2 * k),
            2 ** n * math.factorial(k) * math.factorial(n - k)
            * math.factorial(n - 2 * k)
        )
        result += coefficient * x ** (n - 2 * k)
    return result


def exact_reference(name: str, n: int) -> F:
    if name == "nonreal_roots":
        return complex_power(F(3, 10), F(2, 5), n)[0]
    if name == "infinitely_many_zeros":
        return complex_power(F(0), F(1, 2), n)[0]
    if name == "repeated_root_with_cancellation":
        return F(n - 3, 3 * 4 ** n)
    if name == "balanced_hypergeometric":
        return F(1, 3 ** n) * rising(F(2), n) / rising(F(5, 2), n)
    if name == "scaled_catalan":
        return F(math.comb(2 * n, n), (n + 1) * 8 ** n)
    if name == "scaled_legendre":
        return F(1, 3 ** n) * legendre_coefficient_formula(n, F(1, 4))
    if name == "negative_denominators":
        return F(-1, 2) ** n
    raise KeyError(name)


EXAMPLES = [
    Example(
        "nonreal_roots",
        ((F(1, 4),), (F(-3, 5),), (F(1),)),
        (F(1), F(3, 10)), 4, F(1, 2), F(1, 64)
    ),
    Example(
        "infinitely_many_zeros",
        ((F(1, 4),), (F(0),), (F(1),)),
        (F(1), F(0)), 4, F(1, 2), F(1, 64)
    ),
    Example(
        "repeated_root_with_cancellation",
        ((F(1, 16),), (F(-1, 2),), (F(1),)),
        (F(-1), F(-1, 6)), 16, F(1, 2), F(1, 1024)
    ),
    Example(
        "balanced_hypergeometric",
        ((F(-2, 3), F(-1, 3)), (F(5, 2), F(1))),
        (F(1),), 4, F(1, 3), F(1, 16)
    ),
    Example(
        "scaled_catalan",
        ((F(-1), F(-2)), (F(8), F(4))),
        (F(1),), 8, F(1, 2), F(1, 32)
    ),
    Example(
        "scaled_legendre",
        ((F(1, 9), F(1, 9)), (F(-1, 4), F(-1, 6)), (F(2), F(1))),
        (F(1), F(1, 12)), 18, F(1, 3), F(1, 1024)
    ),
    Example(
        "negative_denominators",
        ((F(-1),), (F(-2),)),
        (F(1),), 2, F(1, 2), F(1, 8)
    ),
]


def grid_resolution(alpha: F, scale: F, b: int) -> int:
    target = F(4, 1) / (alpha - scale) * scale ** (-b)
    result = 1
    while result < target:
        result *= 2
    return result


def cell_key(x: F, resolution: int) -> int:
    fraction = x - x.numerator // x.denominator
    scaled = resolution * fraction
    return scaled.numerator // scaled.denominator


def verify_example(example: Example) -> dict:
    count, levels = 128, 6
    values = scalar_recurrence(example, count)
    numerators, denominators = matrix_numerators(example, count)
    need(len(example.polynomials) == example.order + 1, "recurrence dimensions")
    reference_terms = 24
    for n in range(reference_terms):
        need(values[n] == exact_reference(example.name, n),
             f"{example.name}: independent closed expression at n={n}")
    for n in range(count):
        need(denominators[n] != 0, "matrix denominator nonzero")
        need(numerators[n] / denominators[n] == values[n],
             f"{example.name}: numerator product at n={n}")

    d, r, alpha, q = (
        example.order, example.parameter_bound, example.alpha, example.scale
    )
    block_norms = [
        max(abs(a) for a in values[n:n + d]) for n in range(count - d + 1)
    ]
    need(block_norms[0] == 1, "normalized initial block")
    need(0 < q < alpha / 2, "scale below half inverse-step bound")
    for n in range(count - d):
        ad = abs(evaluate(example.polynomials[d], n))
        a0 = abs(evaluate(example.polynomials[0], n))
        need(ad >= F(1, r), "denominator lower bound")
        need(a0 >= ad / r, "inverse coefficient lower bound")
        for j in range(d):
            need(abs(evaluate(example.polynomials[j], n)) <= r * ad,
                 "normalized coefficient upper bound")
        need(block_norms[n + 1] >= alpha * block_norms[n],
             "one-step block lower bound")
        need(block_norms[n] <= example.envelope_base ** n,
             "finite exponential envelope check")

    t_bound = 1
    while example.envelope_base ** t_bound > q:
        t_bound += 1
    samples = []
    selected_indices = []
    for j in range(1, levels + 1):
        threshold = q ** j
        n = next(
            n for n in range(1, t_bound * j + 1)
            if block_norms[n] <= threshold
        )
        need(block_norms[n - 1] > threshold, "first crossing")
        need(alpha * threshold < block_norms[n] <= threshold,
             "strict block annulus")
        k = next(k for k in range(d)
                 if abs(values[n + k]) > alpha * threshold)
        sample = values[n + k]
        need(alpha * threshold < abs(sample) <= threshold,
             "selected signed scalar annulus")
        selected_indices.append(n + k)
        samples.append({
            "level": j, "block_index": n, "coordinate": k,
            "original_index": n + k, "value": str(sample),
            "block_norm": str(block_norms[n]),
            "threshold_equality": block_norms[n] == threshold
        })
    need(len(set(selected_indices)) == levels, "distinct original sample indices")
    for i, j in itertools.combinations(range(levels), 2):
        ai, aj = values[selected_indices[i]], values[selected_indices[j]]
        need(abs(ai - aj) > (alpha - q) * q ** (i + 1),
             "signed reverse-triangle separation")

    # Actual periodic keys at a common finer resolution, including signed shifts.
    resolution = grid_resolution(alpha, q, levels)
    center, scale = F(1, 7), F(3, 2)
    keys = [cell_key(center, resolution)] + [
        cell_key(center + scale * values[n], resolution) for n in selected_indices
    ]
    need(len(set(keys)) == levels + 1, "distinct periodic grid addresses")

    # The squared clearing rule must retain signs for negative D_n and equality.
    sign_tests = 0
    equality_tests = 0
    for n in range(24):
        p_n, d_n, f_n = numerators[n], denominators[n], values[n]
        for threshold in (F(0), abs(f_n), q, alpha * q):
            direct = f_n * f_n - threshold * threshold
            cleared = p_n * p_n - threshold * threshold * d_n * d_n
            need(sign(direct) == sign(cleared), "squared absolute comparison")
            sign_tests += 1
            equality_tests += direct == 0
        for t in (F(1), F(3, 2), F(2)):
            for boundary in (t * f_n, t * f_n + F(1, 17),
                             t * f_n - F(1, 19)):
                direct = t * f_n - boundary
                cleared = t * p_n * d_n - boundary * d_n * d_n
                need(sign(direct) == sign(cleared), "signed address comparison")
                sign_tests += 1
                equality_tests += direct == 0

    return {
        "name": example.name, "order": d,
        "independent_reference_terms": reference_terms,
        "matrix_product_terms": count,
        "parameter_bound_R": r, "alpha": str(alpha),
        "envelope_base": str(example.envelope_base), "Q": str(q),
        "index_multiplier_T": t_bound, "sampled_levels": levels,
        "samples": samples,
        "negative_terms_in_prefix": sum(a < 0 for a in values),
        "zero_terms_in_prefix": sum(a == 0 for a in values),
        "negative_denominators_in_prefix": sum(a < 0 for a in denominators),
        "cleared_sign_comparisons": sign_tests,
        "equality_comparisons": equality_tests,
        "distinct_grid_keys": len(set(keys))
    }


def verify_boundary_keys() -> dict:
    cases = 0
    for resolution in (2, 4, 8):
        for translate in (-1, 0, 1):
            for j in range(resolution + 1):
                boundary = translate + F(j, resolution)
                step = F(1, 3 * resolution)
                need(cell_key(boundary, resolution) == j % resolution,
                     "boundary belongs to its right-hand cell")
                need(cell_key(boundary - step, resolution)
                     == (j - 1) % resolution, "left-hand neighbor cell")
                need(cell_key(boundary + step, resolution) == j % resolution,
                     "right-hand neighbor cell")
                cases += 1
    return {"boundary_triples": cases,
            "integer_wrap_and_negative_coordinates": True}


def window_lengths(branching: int, height: int, gap: int, base: int):
    lengths = {1: base}
    spans = {1: branching * base + (branching - 1) * gap}
    for h in range(2, height + 1):
        lengths[h] = gap + spans[h - 1]
        spans[h] = 2 * branching * spans[h - 1] + (3 * branching - 1) * gap
    return lengths, spans


def build_windows(branching: int, height: int, gap: int, base: int):
    lengths, spans = window_lengths(branching, height, gap, base)
    records = []
    cursor = 1

    def visit(h: int, path: tuple[int, ...]) -> None:
        nonlocal cursor
        for child in range(branching):
            start = cursor
            end = start + lengths[h] - 1
            index = len(records)
            records.append({
                "path": path + (child,), "height": h, "start": start,
                "end": end, "subtree_end": None, "length": lengths[h]
            })
            cursor = end + gap + 1
            if h > 1:
                visit(h - 1, path + (child,))
            records[index]["subtree_end"] = records[-1]["end"]

    visit(height, ())
    total = records[-1]["end"]
    need(total == spans[height], "preorder total span agrees with recurrence")
    for record in records:
        local_span = record["subtree_end"] - record["start"] + 1
        need(local_span <= 2 * record["length"], "local subtree span")
    return records, spans[height]


def verify_window_spans() -> dict:
    cases = 0
    maximum_edges, maximum_span = 0, 0
    for m, height, gap, base in itertools.product((2, 3), (1, 2, 3), (1, 4), (1, 3)):
        records, total = build_windows(m, height, gap, base)
        coefficient = m * (2 * m) ** (height - 1)
        constant = (
            (m - 1) * (2 * m) ** (height - 1)
            + (3 * m - 1) * ((2 * m) ** (height - 1) - 1) // (2 * m - 1)
        ) * gap
        need(total == coefficient * base + constant, "closed affine span formula")
        need(len(records) == sum(m ** j for j in range(1, height + 1)),
             "complete tree edge count")
        cases += 1
        maximum_edges = max(maximum_edges, len(records))
        maximum_span = max(maximum_span, total)
    return {
        "exact_cases": cases, "largest_edge_count": maximum_edges,
        "largest_span": maximum_span
    }


def exhaustive_routing_probability() -> dict:
    """Two nondefault children, two samples each, adaptive descendant routing.

    Root center selector entries are exposed as zero. All other exposed center
    entries have key zero. Samples have keys one or two and consult independent
    selector entries. Different samples reaching the same leaf retain different
    terminal keys; different children have disjoint terminal tables.
    """
    samples = list(itertools.product(range(2), range(2)))
    selector_bits = 12  # 4 root local entries + 8 descendant local entries
    weighted_failures = 0
    distinct_address_cases = 0
    total_event_count = 0
    for bits in itertools.product((0, 1), repeat=selector_bits):
        root = bits[:4]
        addresses = []
        for sample_number, (child, sample) in enumerate(samples):
            s1, s2 = bits[4 + 2 * sample_number:6 + 2 * sample_number]
            leaf = 0 if s1 else (1 if s2 else 2)
            # Key zero is reserved for the exposed center in every table.
            addresses.append((child, leaf, sample + 1))
        need(len(set(addresses)) == len(samples), "distinct addressed terminal bits")
        need(all(address[-1] != 0 for address in addresses), "unexposed sample key")
        distinct_address_cases += 1
        for terminal_bits in itertools.product((0, 1), repeat=4):
            terminal_table = dict(zip(addresses, terminal_bits))
            local_hits = [
                root[i] * terminal_table[addresses[i]] for i in range(4)
            ]
            # p=1/3 gives integer terminal weight 2^(number of zero bits)/3^4.
            weight = 2 ** (4 - sum(terminal_bits))
            if not any(local_hits):
                weighted_failures += weight
            total_event_count += 1
    probability = F(weighted_failures, 2 ** selector_bits * 3 ** 4)
    expected = (1 - F(1, 3) / 2) ** 4
    need(probability == expected, "exact conditional routing failure identity")

    # Deliberately violate terminal distinctness: samples 0,1 and 2,3 share bits.
    shared_failure_weight = 0
    for root in itertools.product((0, 1), repeat=4):
        for terminal in itertools.product((0, 1), repeat=2):
            hits = [root[i] * terminal[i // 2] for i in range(4)]
            weight = 2 ** (2 - sum(terminal))
            if not any(hits):
                shared_failure_weight += weight
    shared_probability = F(shared_failure_weight, 2 ** 4 * 3 ** 2)
    need(shared_probability == (1 - 3 * F(1, 3) / 4) ** 2,
         "independent overlapping-address negative-control calculation")
    need(shared_probability != expected, "address distinctness is necessary")
    return {
        "terminal_probability": "1/3", "nondefault_children": 2,
        "samples_per_child": 2, "selector_configurations": 2 ** selector_bits,
        "terminal_event_cases": total_event_count,
        "distinct_address_cases": distinct_address_cases,
        "exhaustive_failure_probability": str(probability),
        "formula_failure_probability": str(expected),
        "negative_control_shared_terminal_probability": str(shared_probability),
        "negative_control_detected": True
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path("data/verification_results.json"))
    args = parser.parse_args()
    results = {
        "schema": "universal-recurrence-avoidance-exact-verification-v1",
        "arithmetic": "Python fractions.Fraction; exact rational arithmetic",
        "scope": (
            "Finite corroboration of example recurrences, signed block selection, "
            "denominator clearing, window spans, and the conditional routing "
            "identity. No infinite set is instantiated; no infinite theorem is "
            "formally verified; no quantifier-elimination engine is implemented."
        ),
        "examples": [verify_example(example) for example in EXAMPLES],
        "half_open_periodic_boundaries": verify_boundary_keys(),
        "preorder_windows": verify_window_spans(),
        "exhaustive_routing": exhaustive_routing_probability(),
        "status": "all exact checks passed"
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": results["status"], "examples": len(results["examples"]),
        "reference_terms": sum(x["independent_reference_terms"] for x in results["examples"]),
        "sign_comparisons": sum(x["cleared_sign_comparisons"] for x in results["examples"]),
        "window_cases": results["preorder_windows"]["exact_cases"],
        "routing_failure": results["exhaustive_routing"]["exhaustive_failure_probability"],
        "output": str(args.output)
    }, indent=2))


if __name__ == "__main__":
    main()

