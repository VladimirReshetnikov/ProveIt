#!/usr/bin/env python3
"""Reproduce exact verification and data. No third-party dependencies.

Run from any directory: python code/verify.py
A smaller run is available as:  python code/verify.py --quick
The assertions check finite instances, not the infinite nonrationality,
non-P-recursiveness or natural-boundary theorems. Those are proved in
article.tex / article.pdf.
"""
import argparse
import csv
import hashlib
import json
import platform
import random
from collections import Counter
from pathlib import Path
from time import perf_counter

from mixed_base import (count_one, dense_coefficients, digit_support,
                        even_count_stream, exceptional_parity_indices,
                        exponent, full_from_even, gap, interleaved_count,
                        interval_histogram, multiply_digit_factor,
                        ternary_even_without_logs, threshold, threshold_stream)

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "data"

RANDOM_SEED = 20260919
COMPARISON_PAIRS = [(2, 3), (2, 4), (2, 5), (2, 8), (2, 9), (2, 16),
                    (3, 4), (3, 9)]


def main(quick: bool = False) -> None:
    start = perf_counter()
    DATA.mkdir(parents=True, exist_ok=True)
    result = {}
    dense_checks = 0
    sparse_checks = 0
    gap_checks = 0
    max_dense_degree = 0
    grid_digest = hashlib.sha256()

    # ------------------------------------------------------------------
    # Direct multiplication versus event sweep versus the theorem,
    # including the empty-product cases m=0 and n=0.
    # ------------------------------------------------------------------
    for a in range(2, 7):
        for q in range(a + 1, a + 6):
            for m in range(5):
                for n in range(5):
                    coefficients = dense_coefficients(a, q, m, n)
                    direct = dict(Counter(coefficients))
                    swept = interval_histogram(a, q, m, n)
                    assert direct == swept, (a, q, m, n)
                    assert direct.get(1, 0) == count_one(a, q, m, n)
                    assert sum(coefficients) == a**(m + n)
                    max_dense_degree = max(max_dense_degree, len(coefficients) - 1)
                    grid_digest.update(f"{a},{q},{m},{n}:{sorted(direct.items())}\n".encode())
                    dense_checks += 1

    # Larger binary/ternary rectangles: the sweep never uses the gap-count theorem.
    sparse_m = 20 if quick else 24
    for m in range(1, sparse_m + 1):
        for n in range(1, 17):
            histogram = interval_histogram(2, 3, m, n)
            assert histogram.get(1, 0) == count_one(2, 3, m, n)
            degree = 2**m - 1 + (3**n - 1) // 2
            assert sum(histogram.values()) == degree + 1
            assert sum(k * v for k, v in histogram.items()) == 2**(m + n)
            sparse_checks += 1

    # ------------------------------------------------------------------
    # An independent interval-sweep grid over the binary family, matching
    # the ranges reported in the article.
    # ------------------------------------------------------------------
    grid_max = 7 if quick else 10
    sweep_grid_cases = 0
    for q in range(3, 13):
        for m in range(grid_max + 1):
            for n in range(grid_max + 1):
                histogram = interval_histogram(2, q, m, n)
                assert histogram.get(1, 0) == count_one(2, q, m, n), (q, m, n)
                assert sum(k * v for k, v in histogram.items()) == 1 << (m + n)
                sweep_grid_cases += 1

    # Seeded randomized sweep: wider bases and lengths than the dense grid.
    randomizer = random.Random(RANDOM_SEED)
    random_cases = 30 if quick else 150
    random_max_n = 11 if quick else 15
    for _ in range(random_cases):
        q = randomizer.randint(3, 40)
        m = randomizer.randint(0, 30)
        n = randomizer.randint(0, random_max_n)
        histogram = interval_histogram(2, q, m, n)
        assert histogram.get(1, 0) == count_one(2, q, m, n), (q, m, n)
        assert sum(k * v for k, v in histogram.items()) == 1 << (m + n)

    # ------------------------------------------------------------------
    # Carry-gap multiplicities from directly enumerated digit supports,
    # plus the index-by-index ruler identity s_i - s_(i-1) = g_(v_a(i)).
    # ------------------------------------------------------------------
    for a in range(2, 7):
        for q in range(a + 1, a + 6):
            for n in range(1, 7):
                support = digit_support(a, q, n)
                differences = [y - x for x, y in zip(support, support[1:])]
                actual = Counter(differences)
                expected = {gap(a, q, t): (a - 1) * a**(n - 1 - t)
                            for t in range(n)}
                assert actual == expected, (a, q, n)
                for i, difference in enumerate(differences, start=1):
                    valuation, rest = 0, i
                    while rest % a == 0:
                        rest //= a
                        valuation += 1
                    assert difference == gap(a, q, valuation), (a, q, n, i)
                assert all(x == 1 or y == 1
                           for x, y in zip(differences, differences[1:]))
                gap_checks += 1

    # The same ruler identity over a much wider range of second bases, a=2.
    ruler_cases = 0
    ruler_n = 10 if quick else 12
    for q in range(3, 16):
        for n in range(1, ruler_n + 1):
            support = digit_support(2, q, n)
            differences = [y - x for x, y in zip(support, support[1:])]
            assert Counter(differences) == Counter(
                {gap(2, q, t): 1 << (n - t - 1) for t in range(n)})
            for i, difference in enumerate(differences, start=1):
                assert difference == gap(2, q, (i & -i).bit_length() - 1)
            ruler_cases += 1

    # ------------------------------------------------------------------
    # Expand the actual interleaved product, not its rectangular rearrangement.
    # ------------------------------------------------------------------
    prefix_max = 22 if quick else 28
    coefficients = [1]
    rows = [(0, 0, 1, [0])]
    for N in range(1, prefix_max + 1):
        coefficients = multiply_digit_factor(coefficients, exponent(2, 3, N), 2)
        locations = [j for j, value in enumerate(coefficients) if value == 1]
        assert len(locations) == interleaved_count(2, 3, N)
        rows.append((N, len(coefficients) - 1, len(locations), locations))
        max_dense_degree = max(max_dense_degree, len(coefficients) - 1)
    assert rows[10][3] == [0, 71, 81, 152]
    with (DATA / "direct_prefix_checks.json").open("w", encoding="utf-8") as out:
        json.dump([dict(N=N, degree=d, count=v, positions=p) for N, d, v, p in rows],
                  out, indent=2)
        out.write("\n")
    del coefficients

    # ------------------------------------------------------------------
    # Every threshold decision is checked against both adjacent integer powers.
    # ------------------------------------------------------------------
    threshold_checks = 0
    main_thresholds = []
    main_stop = 20000 if quick else 100000
    other_stop = 300 if quick else 1000
    for a, q, stop in [(2, 3, main_stop)] + [
            (a, q, other_stop) for a in range(2, 9) for q in range(a + 1, a + 8)]:
        last = 0
        a_power = 1
        for m, t, q_power in threshold_stream(a, q, stop):
            assert (q - a) * q_power + a - 1 >= (q - 1) * a_power
            if t:
                assert (q - a) * (q_power // q) + a - 1 < (q - 1) * a_power
            if m >= 2:  # The step 0 -> 1 may jump by more than one for general bases.
                assert t - last in (0, 1)
            if (a, q, stop) == (2, 3, main_stop) and m <= 10000:
                main_thresholds.append(t)
            last = t
            a_power *= a
            threshold_checks += 1

    # ------------------------------------------------------------------
    # Integer verification of the floor formula: for n>=2, floor((n+1)log_3 2)
    # is the largest d with 3**d < 2**(n+1). No floating-point logarithm.
    # ------------------------------------------------------------------
    floor_checks = 0
    floor_power, d, two_power = 1, 0, 2
    for n in range(10001):
        while 3 * floor_power < two_power:
            floor_power *= 3
            d += 1
        base_value = 2**(n - d)
        actual = 1 if n == 0 else 2**(n - main_thresholds[n] + 1)
        assert actual == base_value + int(n == 1)
        if n >= 2:
            assert floor_power < two_power < 3 * floor_power
        two_power *= 2
        floor_checks += 1

    # The deliberately independent ternary route: least s with 3**s >= 2**(n+1).
    closed_form_limit = 300 if quick else 2000
    for n in range(closed_form_limit + 1):
        assert ternary_even_without_logs(n) == interleaved_count(2, 3, 2 * n)

    # Check input recurrence and the exact even/odd relation.
    for N in range(1, 1001):
        assert exponent(2, 3, N + 4) == 5 * exponent(2, 3, N + 2) - 6 * exponent(2, 3, N)
    for n in range(1000):
        assert interleaved_count(2, 3, 2 * n + 1) == (
            interleaved_count(2, 3, 2 * n + 2) // 2 + int(n <= 3))

    # ------------------------------------------------------------------
    # The binary family: streaming recurrence, quotient set, general parity
    # identity, and the order-four exponent recurrence.
    # ------------------------------------------------------------------
    family_bases = range(3, 33) if quick else range(3, 65)
    family_even_n = 120 if quick else 300
    family_parity_N = 200 if quick else 600
    family_cases = 0
    parity_cases = 0
    streaming_cases = 0
    exponent_recurrence_cases = 0
    exceptional_sets = {}
    for q in family_bases:
        t, g = 1, q - 1
        for n in range(1, family_even_n + 1):
            assert t == threshold(2, q, n), (q, n)
            current = interleaved_count(2, q, 2 * n)
            assert current == 1 << (n - t + 1)
            previous = interleaved_count(2, q, 2 * (n - 1))
            assert current in (previous, 2 * previous)
            if g < 1 << (n + 1):
                t += 1
                g = q * g - 1
            family_cases += 1
        for n, value in enumerate(even_count_stream(2, q, family_parity_N)):
            assert value == interleaved_count(2, q, 2 * n), (q, n)
            streaming_cases += 1
        for N in range(family_parity_N + 1):
            assert interleaved_count(2, q, N) == full_from_even(2, q, N), (q, N)
            parity_cases += 1
        exceptional = exceptional_parity_indices(2, q, 40)
        expected = {3: [1, 2, 3], 4: [1]}.get(q, [])
        assert exceptional == expected, (q, exceptional)
        exceptional_sets[q] = exceptional
        powers = [exponent(2, q, i) for i in range(1, 82)]
        for j in range(len(powers) - 4):
            assert powers[j + 4] == (2 + q) * powers[j + 2] - 2 * q * powers[j]
            exponent_recurrence_cases += 1

    # The streaming recurrence and the general parity identity also hold
    # for digit sets larger than {0,1}.
    general_pairs = [(3, 4), (3, 5), (3, 7), (3, 9), (4, 5), (4, 9), (5, 7), (6, 7)]
    general_cases = 0
    general_exceptional = {}
    general_limit = 60 if quick else 200
    for a, q in general_pairs:
        for n, value in enumerate(even_count_stream(a, q, general_limit)):
            assert value == interleaved_count(a, q, 2 * n), (a, q, n)
        for N in range(general_limit + 1):
            assert interleaved_count(a, q, N) == full_from_even(a, q, N), (a, q, N)
            general_cases += 1
        exceptional = exceptional_parity_indices(a, q, 40)
        # The set must be finite; check that the search window closes it.
        assert not exceptional or max(exceptional) <= 30, (a, q, exceptional)
        assert exceptional == list(range(1, len(exceptional) + 1)), (a, q, exceptional)
        general_exceptional[f"{a},{q}"] = exceptional
        for i in range(1, general_limit):
            assert exponent(a, q, i + 4) == (
                (a + q) * exponent(a, q, i + 2) - a * q * exponent(a, q, i))

    # ------------------------------------------------------------------
    # Rational subfamilies.
    # ------------------------------------------------------------------
    rational_cases = 0
    rational_d = 7 if quick else 10
    rational_n = 200 if quick else 600
    for s in range(2, rational_d + 1):
        q = 1 << s
        for n in range(rational_n + 1):
            value = interleaved_count(2, q, 2 * n)
            assert value == 1 << (n - n // s)
            assert interleaved_count(2, q, 2 * (n + s)) == (1 << (s - 1)) * value
            rational_cases += 1

    dependent = []
    dependent_cases = 0
    for a, q, u, v in [(2, 4, 1, 2), (2, 8, 1, 3), (3, 9, 1, 2), (4, 8, 2, 3),
                       (4, 16, 1, 2), (8, 16, 3, 4), (9, 27, 2, 3)]:
        assert q**u == a**v
        tested_from = 40
        for N in range(tested_from, 201):
            assert interleaved_count(a, q, N + 2 * v) == a**(v - u) * interleaved_count(a, q, N)
            dependent_cases += 1
        dependent.append(dict(a=a, q=q, u=u, v=v, from_N=tested_from, to_N=200,
                              step=2 * v, multiplier=a**(v - u)))

    # ------------------------------------------------------------------
    # Exported data.
    # ------------------------------------------------------------------
    with (DATA / "sequence.csv").open("w", newline="", encoding="utf-8") as out:
        writer = csv.writer(out)
        writer.writerow(["N", "G_N_empty_at_zero", "nu_1_N"])
        for N in range(1001):
            writer.writerow([N, exponent(2, 3, N) if N else "", interleaved_count(2, 3, N)])
    with (DATA / "even_subsequence.csv").open("w", newline="", encoding="utf-8") as out:
        writer = csv.writer(out)
        writer.writerow(["n", "threshold_t_n", "nu_1_2n", "power_of_2_exponent"])
        for n, t in enumerate(main_thresholds[:1001]):
            e = n - t + 1 if n else 0
            writer.writerow([n, t, 2**e, e])
    with (DATA / "b_even.txt").open("w", encoding="utf-8") as out:
        out.write("# n a(n), where a(n)=number of coefficients equal to 1 in P_(2n)\n")
        out.write("# No OEIS identifier is claimed or assigned.\n")
        for n, t in enumerate(main_thresholds[:1001]):
            out.write(f"{n} {2**(n-t+1) if n else 1}\n")
    with (DATA / "base_comparison.csv").open("w", newline="", encoding="utf-8") as out:
        writer = csv.writer(out)
        writer.writerow(["n"] + [f"v_{a}_{q}_2n" for a, q in COMPARISON_PAIRS])
        streams = [list(even_count_stream(a, q, 100)) for a, q in COMPARISON_PAIRS]
        for n in range(101):
            writer.writerow([n] + [stream[n] for stream in streams])

    result = dict(
        status="PASS",
        quick_mode=quick,
        python_version=platform.python_version(),
        dense_rectangles=dense_checks,
        larger_sparse_rectangles=sparse_checks,
        carry_gap_checks=gap_checks,
        ruler_identity_checks=ruler_cases,
        independent_sweep_grid_checks=sweep_grid_cases,
        randomized_sweep_checks=random_cases,
        randomized_sweep_seed=RANDOM_SEED,
        interleaved_prefixes=len(rows),
        maximum_dense_degree=max_dense_degree,
        exact_threshold_checks=threshold_checks,
        floor_formula_checks=floor_checks,
        independent_ternary_closed_form_checks=closed_form_limit + 1,
        input_recurrence_checks=1000,
        even_odd_identity_checks=1000,
        binary_family_threshold_checks=family_cases,
        binary_family_streaming_checks=streaming_cases,
        binary_family_parity_checks=parity_cases,
        binary_family_exponent_recurrence_checks=exponent_recurrence_cases,
        binary_family_exceptional_indices={str(k): v for k, v in exceptional_sets.items() if v},
        general_pair_parity_checks=general_cases,
        general_pair_exceptional_indices=general_exceptional,
        power_of_two_rational_checks=rational_cases,
        dependent_family_check_count=dependent_cases,
        dependent_family_checks=dependent,
        dense_histogram_sha256=grid_digest.hexdigest(),
        elapsed_seconds=round(perf_counter() - start, 3),
        arithmetic="All verification decisions use Python exact integers.",
        scope=("Finite identities only; nonrationality, non-P-recursiveness and the "
               "natural boundary are proved in the article."),
    )
    with (DATA / "verification.json").open("w", encoding="utf-8") as out:
        json.dump(result, out, indent=2)
        out.write("\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quick", action="store_true",
                        help="run reduced ranges; the full run is the reported one")
    main(parser.parse_args().quick)
