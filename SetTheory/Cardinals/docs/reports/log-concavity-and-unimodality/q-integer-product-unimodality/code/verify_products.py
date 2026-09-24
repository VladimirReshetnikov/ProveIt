#!/usr/bin/env python3
"""Exact, dependency-free verification for the q-integer unimodality research note.

Run `python3 code/verify_products.py --full --out data/verification_results.json` to reproduce
all reported tests. These finite checks supplement, not replace, the proofs.
Coefficients are stored in increasing exponent order. Python 3.10+.
"""
from __future__ import annotations

import argparse
import csv
import itertools
import json
import math
from pathlib import Path
import random
import sys
from typing import Iterable, Sequence

Poly = list[int]


def require(condition: bool, message: str) -> None:
    """Do not use assert: verification must also work under `python -O`."""
    if not condition:
        raise AssertionError(message)


def positive(value: int, name: str) -> None:
    if not isinstance(value, int) or isinstance(value, bool) or value < 1:
        raise ValueError(f"{name} must be a positive integer")


def convolve(a: Sequence[int], b: Sequence[int]) -> Poly:
    """Independent schoolbook multiplication, used for small cross-checks."""
    if not a or not b:
        raise ValueError("Coefficient sequences must be nonempty")
    result = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            result[i+j] += x*y
    return result


def q_integer(a: int, r: int = 1) -> Poly:
    positive(a, "a")
    positive(r, "r")
    result = [0] * (r*(a-1)+1)
    result[::r] = [1]*a
    return result


def multiply_uniform(f: Sequence[int], a: int) -> Poly:
    """Multiply by [a]_q using a sliding sum, in linear arithmetic time."""
    positive(a, "a")
    if not f:
        raise ValueError("Coefficient sequence must be nonempty")
    out = [0]*(len(f)+a-1)
    current = 0
    for j in range(len(out)):
        if j < len(f):
            current += f[j]
        if 0 <= j-a < len(f):
            current -= f[j-a]
        out[j] = current
    return out


def ordinary_product(a: Iterable[int]) -> Poly:
    out = [1]
    for value in a:
        out = multiply_uniform(out, value)
    return out


def multiply_comb(f: Sequence[int], b: int, r: int) -> Poly:
    """Multiply by [b]_(q^r); recurrence follows (1-q^r)P=(1-q^(rb))F."""
    positive(b, "b")
    positive(r, "r")
    if not f:
        raise ValueError("Coefficient sequence must be nonempty")
    out = [0] * (len(f)+r*(b-1))
    for j in range(len(out)):
        out[j] = ((f[j] if j < len(f) else 0)
                  + (out[j-r] if j >= r else 0)
                  - (f[j-r*b] if 0 <= j-r*b < len(f) else 0))
    return out


def product(a: Sequence[int], b: int, r: int) -> Poly:
    return multiply_comb(ordinary_product(a), b, r)


def unimodal(c: Sequence[int]) -> bool:
    """Direct rise-then-fall test; does not assume symmetry."""
    falling = False
    for x, y in zip(c, c[1:]):
        if y < x:
            falling = True
        elif y > x and falling:
            return False
    return True


def symmetric_unimodal(c: Sequence[int]) -> bool:
    return (list(c) == list(reversed(c))
            and all(c[j] >= c[j-1] for j in range(1, (len(c)-1)//2+1)))


def conjectured_condition(a: Sequence[int], b: int, r: int) -> bool:
    return any(x % r == 0 for x in a) or b <= 1+sum(x//r for x in a)


def r3_data(a: Sequence[int], b: int) -> dict:
    """Closed-form decision and a coefficient-drop witness when negative."""
    positive(b, "b")
    for value in a:
        positive(value, "a_i")
    if any(x % 3 == 0 for x in a):
        return {"unimodal": True, "divisible_factor": True,
                "bound": None, "drop_index": None}
    Q = sum(x//3 for x in a)
    t = sum(x % 3 == 2 for x in a)
    h, v = divmod(t, 6)
    M = Q+2*h
    good = b <= M+1
    return {"unimodal": good, "divisible_factor": False,
            "Q": Q, "t": t, "bound": M+1,
            "drop_index": None if good else 3*M+(v+3)//2}


def validate_r3(a: Sequence[int], b: int, f: Sequence[int] | None = None) -> bool:
    data = r3_data(a, b)
    c = multiply_comb(f, b, 3) if f is not None else product(a, b, 3)
    require(c == c[::-1], f"Symmetry failed: {a=}, {b=}")
    require(unimodal(c) == data["unimodal"], f"r=3 criterion failed: {a=}, {b=}")
    require(unimodal(c) == symmetric_unimodal(c), "Unimodality implementations differ")
    j = data["drop_index"]
    if j is not None:
        require(1 <= j <= (len(c)-1)//2, "Drop is not in the first half")
        require(c[j]-c[j-1] == -1, f"Unit-drop certificate failed: {a=}, {b=}, {j=}")
    return conjectured_condition(a, b, 3) != data["unimodal"]


def counterexample_certificate() -> dict:
    c = product([2]*6, 2, 3)
    expected = [1, 6, 15, 21, 21, 21, 21, 15, 6, 1]
    # A genuinely separate combinatorial enumeration: 7 binary choices.
    enumeration = [0]*10
    for choices in itertools.product(range(2), repeat=7):
        enumeration[sum(choices[:6])+3*choices[6]] += 1
    binomial = [(math.comb(6, j) if 0 <= j <= 6 else 0)
                + (math.comb(6, j-3) if 0 <= j-3 <= 6 else 0)
                for j in range(10)]
    require(c == expected == enumeration == binomial, "Counterexample expansion failed")
    require(unimodal(c), "Counterexample is not unimodal")
    require(not conjectured_condition([2]*6, 2, 3), "Counterexample satisfies condition")
    return {
        "source": "Connelly et al., arXiv:2605.12822v1, Conjecture 5.4, p. 14",
        "r": 3, "k": 6, "a": [2]*6, "b": 2, "degree": 9,
        "coefficients_low_to_high": c,
        "left_half_differences_including_constant": [1, 5, 9, 6, 0],
        "symmetric": True, "weakly_unimodal": True,
        "any_a_divisible_by_r": False, "floor_sum": 0,
        "conjectured_condition": False, "claimed_necessity_regime_k_le_3_or_r_le_3": True,
        "independent_expansions": ["sliding convolution", "128 binary choices", "binomial theorem"],
        "corrected_r3_bound": 3,
    }


def run(full: bool) -> dict:
    counts: dict[str, int] = {}
    result = {"status": "PASS", "mode": "full" if full else "quick",
              "arithmetic": "exact arbitrary-precision integers; no external dependencies",
              "seed": 1977, "counts": counts}
    counterexample_certificate()
    counts["counterexample_independent_expansions"] = 3
    rng = random.Random(1977)

    # Check optimized multiplication against independent schoolbook convolution.
    counts["independent_multiplication_checks"] = 0
    for _ in range(1000 if full else 100):
        aa = [rng.randint(1, 9) for _ in range(rng.randint(0, 5))]
        b, r = rng.randint(1, 8), rng.randint(2, 9)
        c = [1]
        for a in aa:
            c = convolve(c, q_integer(a))
        c = convolve(c, q_integer(b, r))
        require(c == product(aa, b, r), "Independent multiplication mismatch")
        counts["independent_multiplication_checks"] += 1

    counts["peeling_identity_grid"] = 0
    for r in range(2, 13 if full else 6):
        for a in range(r+1, 4*r+1):
            for b in range(2, 15 if full else 6):
                left = product([a], b, r)
                remainder = product([a-r], b-1, r)
                right = [1]*(a+r*(b-1))
                for j, value in enumerate(remainder):
                    right[j+r] += value
                require(left == right, "Centered peeling identity failed")
                counts["peeling_identity_grid"] += 1

    # Exhaustive multisets remove only permutations of the ordinary factors.
    values = [1, 2, 4, 5, 7, 8]
    max_k = 8 if full else 5
    counts["r3_exhaustive_products"] = 0
    counts["r3_exhaustive_counterexamples_to_original_necessity"] = 0
    for k in range(max_k+1):
        for aa in itertools.combinations_with_replacement(values, k):
            f = ordinary_product(aa)
            bound = r3_data(aa, 1)["bound"]
            for b in range(1, bound+3):
                counter = validate_r3(aa, b, f)
                counts["r3_exhaustive_products"] += 1
                counts["r3_exhaustive_counterexamples_to_original_necessity"] += counter
    result["r3_exhaustive_specification"] = {
        "ordinary_factor_values": values, "k_min": 0, "k_max": max_k,
        "factors": "all multisets", "b": "1 through corrected bound + 2 inclusive"}

    counts["r3_random_products"] = 0
    eligible = [a for a in range(1, 70) if a % 3]
    # New seed isolates the recorded random experiment from other tests.
    rng3 = random.Random(1977)
    for _ in range(30000 if full else 1000):
        aa = [rng3.choice(eligible) for _ in range(rng3.randint(1, 16))]
        bound = r3_data(aa, 1)["bound"]
        b = rng3.randint(1, bound+8)
        validate_r3(aa, b)
        counts["r3_random_products"] += 1
    result["r3_random_specification"] = {
        "seed": 1977, "k": [1, 16], "a": "1..69 excluding multiples of 3",
        "b": "1..corrected bound+8", "sampling": "uniform at each draw"}

    counts["r3_divisible_factor_products"] = 0
    for _ in range(2000 if full else 100):
        aa = [rng.randint(1, 30) for _ in range(rng.randint(1, 12))]
        aa[0] = 3*rng.randint(1, 10)
        validate_r3(aa, rng.randint(1, 70))
        counts["r3_divisible_factor_products"] += 1

    counts["general_r_sufficient_condition"] = 0
    for _ in range(10000 if full else 500):
        r = rng.randint(2, 18)
        aa = [rng.randint(1, 60) for _ in range(rng.randint(1, 12))]
        bound = 1+sum(a//r for a in aa)
        b = rng.randint(1, bound if not any(a % r == 0 for a in aa) else bound+12)
        require(conjectured_condition(aa, b, r), "Invalid generated sufficient case")
        require(unimodal(product(aa, b, r)), f"General sufficient condition failed: {aa=}, {b=}, {r=}")
        counts["general_r_sufficient_condition"] += 1

    counts["general_r_necessary_degree_bound"] = 0
    for _ in range(10000 if full else 500):
        r = rng.randint(2, 18)
        allowed = [a for a in range(1, 61) if a % r]
        aa = [rng.choice(allowed) for _ in range(rng.randint(0, 12))]
        S = sum(a-1 for a in aa)
        b = rng.randint(2+S//r, 11+S//r)
        require(not unimodal(product(aa, b, r)),
                f"Necessary degree bound failed: {aa=}, {b=}, {r=}")
        counts["general_r_necessary_degree_bound"] += 1

    counts["r2_exact_criterion"] = 0
    for _ in range(5000 if full else 300):
        aa = [rng.randint(1, 30) for _ in range(rng.randint(0, 12))]
        b = rng.randint(1, 2+sum(a//2 for a in aa)+10)
        c = product(aa, b, 2)
        pred = conjectured_condition(aa, b, 2)
        require(unimodal(c) == pred, "r=2 criterion failed")
        if not pred:
            j = sum(a-1 for a in aa)+1
            require(c[j]-c[j-1] == -1 and j <= (len(c)-1)//2, "r=2 witness failed")
        counts["r2_exact_criterion"] += 1

    counts["two_shift_boundary_polynomials"] = 0
    counts["two_shift_central_gap_formula"] = 0
    for r in range(2, 61 if full else 15):
        for n, expected in [(r*r-4, False), (r*r-3, True), (r*r-2, True)]:
            f = [math.comb(n, j) for j in range(n+1)]
            c = multiply_comb(f, 2, r)
            require(unimodal(c) == expected, f"Two-shift threshold failed: {r=}, {n=}")
            counts["two_shift_boundary_polynomials"] += 1
        if r >= 3:
            n, N = r*r-4, r*r-3
            c = multiply_comb([math.comb(n, j) for j in range(n+1)], 2, r)
            j, u = (n+r)//2, (N-r-1)//2
            require((c[j]-c[j-1])*N*(N-r+1) == -4*math.comb(N, u),
                    "Two-shift central gap identity failed")
            counts["two_shift_central_gap_formula"] += 1
    result["two_shift_boundary_specification"] = {
        "r_min": 2, "r_max": 60 if full else 14,
        "n_tested": ["r^2-4", "r^2-3", "r^2-2"]}

    counts["binomial_comb_r3_grid"] = 0
    for b in range(1, 41 if full else 12):
        threshold = 6*(b//2)
        for t in sorted({0, 1, max(0, threshold-1), threshold, threshold+1, threshold+7}):
            c = multiply_comb([math.comb(t, j) for j in range(t+1)], b, 3)
            require(unimodal(c) == (t >= threshold), "r=3 binomial-comb threshold failed")
            counts["binomial_comb_r3_grid"] += 1
    return result


def write_tables(directory: Path) -> None:
    with (directory / "r3_binomial_thresholds.csv").open("w", newline="") as handle:
        writer = csv.writer(handle)
        writer.writerow(["b", "least_unimodal_exponent_t", "previous_exponent_gap_index", "previous_exponent_gap"])
        for b in range(1, 41):
            t = 6*(b//2)
            if not t:
                writer.writerow([b, t, "", ""])
                continue
            data = r3_data([2]*(t-1), b)
            c = product([2]*(t-1), b, 3)
            j = data["drop_index"]
            writer.writerow([b, t, j, c[j]-c[j-1]])


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--full", action="store_true", help="Run the full suite described in the report")
    parser.add_argument("--out", type=Path, help="Write JSON results and companion certificate/CSV in this directory")
    args = parser.parse_args()
    result = run(args.full)
    text = json.dumps(result, indent=2, sort_keys=True)+"\n"
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(text, encoding="utf-8")
        (args.out.parent / "certificate.json").write_text(
            json.dumps(counterexample_certificate(), indent=2)+"\n", encoding="utf-8")
        write_tables(args.out.parent)
    print(text, end="")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, ValueError, OSError) as exc:
        print(f"VERIFICATION FAILED: {exc}", file=sys.stderr)
        sys.exit(1)
