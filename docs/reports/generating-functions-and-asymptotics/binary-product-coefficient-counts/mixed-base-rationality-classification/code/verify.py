#!/usr/bin/env python3
"""Reproduce exact verification and data. No third-party dependencies.

Run from any directory: python code/verify.py
The assertions check finite instances, not the infinite nonrationality theorem.
The latter is proved in article.tex / article.pdf.
"""
import csv
import hashlib
import json
from collections import Counter
from pathlib import Path
from time import perf_counter

from mixed_base import (count_one, dense_coefficients, digit_support, exponent,
                        gap, interleaved_count, interval_histogram,
                        multiply_digit_factor, threshold, threshold_stream)

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "data"


def main() -> None:
    start = perf_counter()
    DATA.mkdir(parents=True, exist_ok=True)
    dense_checks = 0
    sparse_checks = 0
    gap_checks = 0
    max_dense_degree = 0
    grid_digest = hashlib.sha256()

    # Direct multiplication versus event sweep versus the theorem, including m=0,n=0.
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
    for m in range(1, 25):
        for n in range(1, 17):
            histogram = interval_histogram(2, 3, m, n)
            assert histogram.get(1, 0) == count_one(2, 3, m, n)
            degree = 2**m - 1 + (3**n - 1) // 2
            assert sum(histogram.values()) == degree + 1
            assert sum(k * v for k, v in histogram.items()) == 2**(m + n)
            sparse_checks += 1

    # Carry-gap multiplicities from directly enumerated digit supports.
    for a in range(2, 7):
        for q in range(a + 1, a + 6):
            for n in range(1, 7):
                support = digit_support(a, q, n)
                actual = Counter(y - x for x, y in zip(support, support[1:]))
                expected = {gap(a, q, t): (a - 1) * a**(n - 1 - t)
                            for t in range(n)}
                assert actual == expected, (a, q, n)
                assert all(x == 1 or y == 1
                           for x, y in zip([v-u for u,v in zip(support,support[1:])],
                                           [v-u for u,v in zip(support[1:],support[2:])]))
                gap_checks += 1

    # Expand the actual interleaved product, not just its rectangular rearrangement.
    coefficients = [1]
    rows = [(0, 0, 1, [0])]
    for N in range(1, 25):
        coefficients = multiply_digit_factor(coefficients, exponent(2, 3, N), 2)
        locations = [j for j, value in enumerate(coefficients) if value == 1]
        assert len(locations) == interleaved_count(2, 3, N)
        rows.append((N, len(coefficients)-1, len(locations), locations))
        max_dense_degree = max(max_dense_degree, len(coefficients)-1)
    assert rows[10][3] == [0, 71, 81, 152]
    with (DATA / "direct_prefix_checks.json").open("w", encoding="utf-8") as out:
        json.dump([dict(N=N, degree=d, count=v, positions=p) for N,d,v,p in rows],
                  out, indent=2)
        out.write("\n")

    # Every threshold decision below is checked against both adjacent integer powers.
    threshold_checks = 0
    main_thresholds = []
    for a, q, stop in [(2, 3, 100000)] + [
            (a, q, 1000) for a in range(2, 9) for q in range(a + 1, a + 8)]:
        last = 0
        a_power = 1
        for m, t, q_power in threshold_stream(a, q, stop):
            assert (q-a)*q_power + a-1 >= (q-1)*a_power
            if t:
                assert (q-a)*(q_power//q) + a-1 < (q-1)*a_power
            if m >= 2:  # The step 0 -> 1 may jump by more than one for general bases.
                assert t-last in (0, 1)
            if (a, q, stop) == (2, 3, 100000) and m <= 10000:
                main_thresholds.append(t)
            last = t
            a_power *= a
            threshold_checks += 1

    # Integer verification of the floor formula: for n>=2, floor((n+1)log_3 2)
    # is the largest d with 3**d < 2**(n+1). No floating-point logarithm is used.
    floor_checks = 0
    floor_power, d, two_power = 1, 0, 2
    for n in range(10001):
        while 3 * floor_power < two_power:
            floor_power *= 3
            d += 1
        base_value = 2**(n-d)
        actual = 1 if n == 0 else 2**(n-main_thresholds[n]+1)
        assert actual == base_value + int(n == 1)
        if n >= 2:
            assert floor_power < two_power < 3*floor_power
        two_power *= 2
        floor_checks += 1

    # Check input recurrence and the exact even/odd relation.
    for N in range(1, 1001):
        assert exponent(2, 3, N+4) == 5*exponent(2, 3, N+2)-6*exponent(2, 3, N)
    for n in range(1000):
        assert interleaved_count(2, 3, 2*n+1) == (
            interleaved_count(2, 3, 2*n+2)//2 + int(n <= 3))

    # Rational dependent-base subfamilies: q**u=a**v.
    dependent = []
    for a, q, u, v in [(2,4,1,2),(2,8,1,3),(3,9,1,2),(4,8,2,3),
                        (4,16,1,2),(8,16,3,4),(9,27,2,3)]:
        assert q**u == a**v
        tested_from = 40
        for N in range(tested_from, 201):
            assert interleaved_count(a,q,N+2*v) == a**(v-u)*interleaved_count(a,q,N)
        dependent.append(dict(a=a,q=q,u=u,v=v,from_N=tested_from,to_N=200,
                              step=2*v,multiplier=a**(v-u)))

    with (DATA / "sequence.csv").open("w", newline="", encoding="utf-8") as out:
        writer = csv.writer(out)
        writer.writerow(["N", "G_N_empty_at_zero", "nu_1_N"])
        for N in range(1001):
            writer.writerow([N, exponent(2,3,N) if N else "", interleaved_count(2,3,N)])
    with (DATA / "even_subsequence.csv").open("w", newline="", encoding="utf-8") as out:
        writer = csv.writer(out)
        writer.writerow(["n", "threshold_t_n", "nu_1_2n", "power_of_2_exponent"])
        for n, t in enumerate(main_thresholds[:1001]):
            e = n-t+1 if n else 0
            writer.writerow([n,t,2**e,e])
    with (DATA / "b_even.txt").open("w", encoding="utf-8") as out:
        out.write("# n a(n), where a(n)=number of coefficients equal to 1 in P_(2n)\n")
        out.write("# No OEIS identifier is claimed or assigned.\n")
        for n, t in enumerate(main_thresholds[:1001]):
            out.write(f"{n} {2**(n-t+1) if n else 1}\n")

    result = dict(status="PASS", dense_rectangles=dense_checks,
                  larger_sparse_rectangles=sparse_checks, carry_gap_checks=gap_checks,
                  interleaved_prefixes=len(rows), maximum_dense_degree=max_dense_degree,
                  exact_threshold_checks=threshold_checks, floor_formula_checks=floor_checks,
                  input_recurrence_checks=1000, even_odd_identity_checks=1000,
                  dependent_family_checks=dependent,
                  dense_histogram_sha256=grid_digest.hexdigest(),
                  elapsed_seconds=round(perf_counter()-start, 3),
                  arithmetic="All verification decisions use Python exact integers.",
                  scope="Finite identities only; nonrationality and natural boundary are proved in the article.")
    with (DATA / "verification.json").open("w", encoding="utf-8") as out:
        json.dump(result, out, indent=2)
        out.write("\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
