#!/usr/bin/env python3
"""Reproduce finite checks for general 132-avoider cap/crossover formulas.

Python 3.10+; standard library only. Exact integers are used for all counts,
cap choices, and finite assertions. Decimal floats are presentation values.
None of these finite regressions proves an asymptotic statement.
"""
from __future__ import annotations

import argparse
from collections import Counter
import csv
from fractions import Fraction
import hashlib
from itertools import permutations, product
import json
from math import comb, factorial, pi, sqrt
from pathlib import Path
import platform

from model import EndpointCounter, avoiders, max_jump


HERE = Path(__file__).resolve().parent
MODEL_SHA256 = "c693d80529b69762600edc4b4d271155e6aa12c9127bda9a59a839ee143538f7"
SOURCE_COMMIT = "7421a4ca60fdf125411edf412f825aac54278b37"
A3 = 729 * sqrt(3) / (4 * pi)
B3 = 5 / sqrt(2 * pi)


def require(condition: bool, message: str) -> None:
    """Keep validation enabled even when Python is invoked with -O."""
    if not condition:
        raise AssertionError(message)


def channel_accepts(mode: str, mask: tuple[int, ...]) -> bool:
    """Finite endpoint channel automaton, gaps ordered core to outside.

    A macro increment is 1 and the cap is 3/2, so one macro fits and any
    pair fails. In high mode the initial deficiency is one macro; low mode
    starts above the cap. A marked gap attempts an append and resets to 0.
    This models only the accepted channel logic once the manuscript's
    pair-sum and endpoint-limit hypotheses have been established.
    """
    deficiency = Fraction(1 if mode == "high" else 2)
    for j, has_append in enumerate(mask):
        if j:
            deficiency += 1
        if has_append:
            if deficiency > Fraction(3, 2):
                return False
            deficiency = Fraction(0)
    return True


def check_channels() -> list[dict]:
    rows = []
    for p in range(2, 15):
        gaps = p - 1
        accepted = {
            mode: [mask for mask in product((0, 1), repeat=gaps)
                   if channel_accepts(mode, mask)]
            for mode in ("low", "high")
        }
        prefixes = {(1,) * j + (0,) * (gaps - j) for j in range(gaps + 1)}
        require(set(accepted["high"]) == prefixes, f"prefix mismatch p={p}")
        require(accepted["low"] == [(0,) * gaps], f"low-mode mismatch p={p}")
        channels = sum(map(len, accepted.values()))
        weight = Fraction(channels, 2) * 2 ** gaps
        require(channels == p + 1, f"channel count p={p}")
        require(weight == 2 ** (p - 2) * (p + 1), f"channel mass p={p}")
        # Remove the common pi^{-(p-1)/2} factor from the amplitude.
        amplitude_rational = weight / 4 ** (p - 1)
        require(amplitude_rational == Fraction(p + 1, 2 ** p), f"C_p p={p}")
        rows.append({"p": p, "gaps": gaps, "low_channels": 1,
                     "high_channels": p, "accepted_channels": channels,
                     "normalized_gap_weight": str(weight),
                     "C_p_rational_factor": str(amplitude_rational)})
    return rows


def literal_avoids132(permutation: tuple[int, ...]) -> bool:
    """Direct pattern test, independent of the Catalan decomposition."""
    n = len(permutation)
    for i in range(n):
        for j in range(i + 1, n):
            for k in range(j + 1, n):
                if permutation[i] < permutation[k] < permutation[j]:
                    return False
    return True


def check_small() -> list[dict]:
    rows = []
    for n in range(1, 9):
        generated = avoiders(n)
        direct = {p for p in permutations(range(1, n + 1)) if literal_avoids132(p)}
        require(len(set(generated)) == len(generated), f"duplicate generator n={n}")
        require(set(generated) == direct, f"literal enumeration mismatch n={n}")
        catalan = comb(2 * n, n) // (n + 1)
        require(len(generated) == catalan, f"Catalan count n={n}")
        histogram = Counter(max_jump(p) for p in generated)
        endpoint_comparisons = 0
        cap_counts = []
        for m in range(n + 1):
            counter = EndpointCounter(n, m)
            selected = [p for p in generated if max_jump(p) <= m]
            require(counter.count() == len(selected), f"total DP n={n}, m={m}")
            cap_counts.append({"m": m, "count": str(len(selected))})
            # First and last deficiencies are n-p[0], n-p[-1].
            for u in range(n):
                for v in range(n):
                    actual = sum(n - p[0] <= u and n - p[-1] <= v for p in selected)
                    require(counter.T(n, u, v) == actual,
                            f"endpoint DP n={n}, m={m}, u={u}, v={v}")
                    endpoint_comparisons += 1
            counter.T.cache_clear()
            counter.unrestricted.cache_clear()
        rows.append({"n": n, "catalan": str(catalan),
                     "literal_permutations_examined": str(factorial(n)),
                     "max_jump_histogram": {str(k): str(histogram[k]) for k in sorted(histogram)},
                     "cap_counts": cap_counts, "endpoint_state_comparisons": endpoint_comparisons})
    avoiders.cache_clear()
    return rows


def exact_window_cap(n: int, t: Fraction) -> int:
    """Exactly floor(n/3 + t*n**(3/4)), for n divisible by three.

    Integer fourth-power comparisons avoid floating-point floor errors.
    """
    require(n % 3 == 0, "window size must be divisible by three")
    numerator = n ** 3 * t.numerator ** 4
    denominator = t.denominator ** 4
    lo, hi = 0, 1
    while hi ** 4 * denominator <= numerator:
        hi *= 2
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if mid ** 4 * denominator <= numerator:
            lo = mid
        else:
            hi = mid
    is_integer = lo ** 4 * denominator == numerator
    shift = lo if t >= 0 else -lo - (not is_integer)
    return n // 3 + shift


def count_row(n: int, m: int, t: Fraction) -> dict:
    counter = EndpointCounter(n, m)
    exact_count, catalan = counter.count(), counter.C[n]
    require(0 <= exact_count <= catalan, f"probability range n={n}, m={m}")
    probability = Fraction(exact_count, catalan)
    row = {"n": n, "m": m, "t": str(t), "exact_count": str(exact_count),
           "catalan_denominator": str(catalan),
           "probability_float": float(probability),
           "scaled_n_to_3_over_2": n ** 1.5 * float(probability),
           "limiting_target_float": B3 + A3 * max(float(t), 0) ** 2}
    counter.T.cache_clear()
    counter.unrestricted.cache_clear()
    return row


def check_constant_algebra() -> dict:
    """Exact rational checks of the constants after the analytic identity.

    The identity I4(1/3)=8*sqrt(2)*pi itself requires the manuscript's proof.
    These checks validate the resulting normalization and simplification.
    """
    # C4*I4: (5/16)*8*sqrt(2)/sqrt(pi) = 5/sqrt(2*pi).
    require(Fraction(5, 16) * 8 * 2 == 5, "B3 rational simplification")
    # A3=C3*3^(13/2)/2!, with C3=1/(2*pi).
    require(Fraction(4, 2 ** 3) * Fraction(3 ** 6, 2) == Fraction(729, 4),
            "A3 rational simplification")
    require(exact_window_cap(48, Fraction(1, 8)) == 18, "positive floor")
    require(exact_window_cap(48, Fraction(-1, 8)) == 13, "negative floor")
    require(exact_window_cap(81, Fraction(-1, 3)) == 18, "integral negative floor")
    return {"I4_at_one_third": "8*sqrt(2)*pi",
            "A3_exact": "729*sqrt(3)/(4*pi)",
            "B3_exact": "5/sqrt(2*pi)", "A3_float": A3, "B3_float": B3,
            "scope": "Rational normalization checks; analytic integral identity is a proof input."}


def write_csv(path: Path, rows: list[dict]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quick", action="store_true", help="omit n=48,...,192 regressions")
    args = parser.parse_args()
    model_hash = hashlib.sha256((HERE / "model.py").read_bytes()).hexdigest()
    require(model_hash == MODEL_SHA256, "credited model.py checksum changed")
    report = {"status": "PASS", "scope": "Finite exact regressions, not an asymptotic proof or error estimate.",
              "python_version": platform.python_version(), "source_commit": SOURCE_COMMIT,
              "model_sha256": model_hash, "constants": check_constant_algebra(),
              "endpoint_channels": check_channels(), "small_n_checks": check_small()}
    print("PASS: channel masks p=2,...,14; literal enumeration and all endpoint states n=1,...,8", flush=True)
    if not args.quick:
        center_rows = []
        for n in (48, 72, 96, 144, 192):
            row = count_row(n, n // 3, Fraction(0))
            center_rows.append(row)
            print(f"n={n}, m={row['m']}: scaled={row['scaled_n_to_3_over_2']:.12f}; target={B3:.12f}", flush=True)
        window_rows = []
        for n in (48, 96):
            for t in (Fraction(-1, 8), Fraction(1, 8)):
                row = count_row(n, exact_window_cap(n, t), t)
                window_rows.append(row)
                print(f"window n={n}, t={t}, m={row['m']}: scaled={row['scaled_n_to_3_over_2']:.12f}", flush=True)
        report["third_boundary_rows"] = center_rows
        report["third_window_rows"] = window_rows
        write_csv(HERE / "third_boundary_counts.csv", center_rows)
        write_csv(HERE / "third_window_counts.csv", window_rows)
    result_name = "quick_results.json" if args.quick else "results.json"
    (HERE / result_name).write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"PASS: wrote {result_name}; no finite-size approximation accuracy is asserted", flush=True)


if __name__ == "__main__":
    main()
