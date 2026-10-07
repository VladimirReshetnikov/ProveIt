#!/usr/bin/env python3
"""Certified rational Fejer tables and exact finite-family restriction search.

Every probability is rational and lies below the true normalized Fejer kernel.
The analytic guarantee is proved in the accompanying article. No floating-point
trigonometric evaluation is used to construct or certify the table.
"""
from __future__ import annotations
import argparse
import itertools
import json
import math
from fractions import Fraction
from pathlib import Path
from energy_inventory import (build_inventory, cyclic_graph_models,
                              deterministic_round, rational, _jsonable)


def atan_reciprocal_interval(a: int, terms: int) -> tuple[Fraction, Fraction]:
    if a <= 1 or terms < 1:
        raise ValueError("need a>1 and at least one term")
    partial = sum((Fraction((-1) ** k, (2 * k + 1) * a ** (2 * k + 1))
                   for k in range(terms)), Fraction(0))
    alternate = partial + Fraction((-1) ** terms, (2 * terms + 1) * a ** (2 * terms + 1))
    return min(partial, alternate), max(partial, alternate)


def pi_interval(tolerance: Fraction) -> tuple[Fraction, Fraction, int]:
    if tolerance <= 0:
        raise ValueError("positive tolerance required")
    terms = 1
    while True:
        a, b = atan_reciprocal_interval(5, terms)
        c, d = atan_reciprocal_interval(239, terms)
        lo, hi = 16 * a - 4 * d, 16 * b - 4 * c
        if hi - lo <= tolerance:
            return lo, hi, terms
        terms += 1


def cosine_interval(k: int, modulus: int, pi_bounds: tuple[Fraction, Fraction],
                    tolerance: Fraction) -> tuple[Fraction, Fraction, int]:
    k %= modulus
    if 2 * k > modulus:
        k -= modulus
    lo, hi = pi_bounds
    x = Fraction(k, modulus) * (lo + hi)
    radius = Fraction(abs(k), modulus) * (hi - lo)
    partial, term, degree = Fraction(1), Fraction(1), 0
    while True:
        remainder = abs(term * x * x / ((2 * degree + 1) * (2 * degree + 2)))
        if remainder <= tolerance:
            err = remainder + radius
            return max(Fraction(-1), partial - err), min(Fraction(1), partial + err), degree
        degree += 1
        term *= -x * x / ((2 * degree - 1) * (2 * degree))
        partial += term


def rational_fejer_table(modulus: int, length: int, denominator: int) -> dict:
    if modulus < 2 or length < 2 or denominator < 1:
        raise ValueError("need modulus>=2, length>=2, denominator>=1")
    Q = denominator
    eps = Fraction(1, 16 * Q)
    pi_lo, pi_hi, pi_terms = pi_interval(eps)
    cosines = [cosine_interval(k, modulus, (pi_lo, pi_hi), eps)
               for k in range(modulus)]
    table, intervals = [], []
    for t in range(modulus):
        lo = Fraction(length)
        hi = Fraction(length)
        for j in range(1, length):
            c_lo, c_hi, _ = cosines[(j * t) % modulus]
            lo += 2 * (length - j) * c_lo
            hi += 2 * (length - j) * c_hi
        lo, hi = max(Fraction(0), lo / length ** 2), min(Fraction(1), hi / length ** 2)
        if t == 0:
            lo = hi = Fraction(1)
        value = Fraction((Q * lo).numerator // (Q * lo).denominator, Q)
        assert 0 <= value <= lo <= hi <= 1 and hi - value < Fraction(2, Q)
        table.append(value)
        intervals.append((lo, hi))
    return {"table": table, "intervals": intervals, "denominator": Q,
            "modulus": modulus, "length": length, "pi_terms": pi_terms,
            "max_cosine_degree": max(x[2] for x in cosines),
            "uniform_error_bound": Fraction(2, Q)}


def search_family(modulus: int, domain: list[int], values: list[int], order: int,
                  eta: Fraction, kernel: list[Fraction], translated: bool = True) -> dict:
    if len(kernel) != modulus or any(not 0 <= q <= 1 for q in kernel):
        raise ValueError("kernel is not an admissible probability table")
    models = cyclic_graph_models(modulus, domain, values, eta)
    best, best_parameters, best_probabilities = None, None, None
    total = Fraction(0)
    count = 0
    for u, v in itertools.product(range(modulus), repeat=2):
        for c in range(modulus) if translated else (0,):
            probabilities = [kernel[(u * x + v * y + c) % modulus]
                             for x, y in zip(domain, values)]
            objective = sum(rational(w) * build_inventory(G, labels, probabilities, order).energy()
                            for G, labels, w in models)
            total += objective
            count += 1
            if best is None or objective > best:
                best, best_parameters, best_probabilities = objective, (u, v, c), probabilities
    assert best is not None and best_probabilities is not None
    result = deterministic_round(models, best_probabilities, order)
    result.update({"parameters": best_parameters, "family_size": count,
                   "family_average": total / count, "best_conditional_expectation": best,
                   "probabilities": best_probabilities,
                   "selected_domain": [domain[i] for i in result["selected_indices"]]})
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    data = json.loads(args.input.read_text())
    kernel = rational_fejer_table(data["modulus"], data["length"], data["denominator"])
    result = search_family(data["modulus"], data["domain"], data["values"], data["order"],
                           rational(data["eta"]), kernel["table"], data.get("translated", True))
    result["kernel_certificate"] = kernel
    text = json.dumps(_jsonable(result), indent=2)
    if args.output:
        args.output.write_text(text + "\n")
    else:
        print(text)


if __name__ == "__main__":
    main()
