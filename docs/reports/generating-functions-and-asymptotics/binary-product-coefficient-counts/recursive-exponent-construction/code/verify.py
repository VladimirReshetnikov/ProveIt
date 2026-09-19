#!/usr/bin/env python3
"""Reproduce the counterexample using exact integer arithmetic.

Default checks need only Python's standard library. Optional --numpy-dense
uses NumPy int64 arrays for a larger *unsaturated*, exact coefficient check.
No floating-point sign tests and no guessed recurrences are used.
"""
from __future__ import annotations

import argparse
import csv
import json
import platform
from collections import defaultdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Iterable

ROOT = Path(__file__).resolve().parents[1]


def trace_values(n: int) -> list[int]:
    """a_0=2, a_1=1, a_n=a_(n-1)-2*a_(n-2), through index n."""
    if n < 0:
        raise ValueError("n must be nonnegative")
    a = [2]
    if n:
        a.append(1)
    for _ in range(2, n + 1):
        a.append(a[-1] - 2 * a[-2])
    return a


def construct(n: int) -> tuple[list[int], list[int], list[int]]:
    """Return trace a, main exponents b (with b_0=0), and interleaved G."""
    a = trace_values(n)
    b = [0]
    g: list[int] = []
    total_main = 0
    for j in range(1, n + 1):
        main = total_main + (1 << j) - 1 + a[j]
        if main <= 0:
            raise ArithmeticError(f"nonpositive main exponent at {j}")
        b.append(main)
        g.extend((1 << (j - 1), main))
        total_main += main
    return a, b, g


def predicted_counts(a: list[int]) -> list[int]:
    n = len(a) - 1
    v = [1]
    for j in range(1, n + 1):
        v.extend((2 if j == 1 else 4,
                  4 if j == 1 else 4 + 4 * int(a[j] > 0)))
    return v


def dense_exact(g: Iterable[int]) -> tuple[list[int], list[int]]:
    """Independent multiplication of all binomials; unbounded Python integers."""
    p = [1]
    counts = [1]
    degrees = [0]
    for exponent in g:
        if exponent <= 0:
            raise ValueError("all exponents must be positive")
        q = [0] * (len(p) + exponent)
        for j, c in enumerate(p):
            q[j] += c
            q[j + exponent] += c
        p = q
        counts.append(p.count(1))
        degrees.append(len(p) - 1)
        assert p[0] == p[-1] == 1
        assert p == p[::-1]
    return counts, degrees


def dense_numpy_exact(g: list[int]) -> tuple[list[int], int, int]:
    """Faster independent exact multiplication; total sum checked against overflow."""
    import numpy as np
    # Sum of all coefficients is 2**len(g), which bounds every coefficient.
    if len(g) >= 63:
        raise ValueError("int64 version requires fewer than 63 binomial factors")
    p = np.array([1], dtype=np.int64)
    counts = [1]
    for m, exponent in enumerate(g, 1):
        q = np.zeros(len(p) + exponent, dtype=np.int64)
        q[:len(p)] += p
        q[exponent:] += p
        p = q
        assert int(p.sum()) == (1 << m)
        assert np.array_equal(p, p[::-1])
        counts.append(int(np.count_nonzero(p == 1)))
    return counts, len(p) - 1, int(p.max())


def interval_count(atoms: dict[int, int], length: int) -> int:
    """Count unit coefficients of (1+...+x^(length-1))*Q by event sweep.

    A weighted atom q at s adds q on the integer interval [s,s+length-1].
    This computes a convolution geometrically, not from the theorem's formula.
    """
    events: dict[int, int] = defaultdict(int)
    for s, weight in atoms.items():
        events[s] += weight
        events[s + length] -= weight
    active = 0
    last = 0
    result = 0
    for position in sorted(events):
        if active == 1:
            result += position - last
        active += events[position]
        if active < 0:
            raise ArithmeticError("negative sweep weight")
        last = position
    assert active == 0
    return result


def sparse_interval_checks(b: list[int]) -> list[int]:
    """Build Q_n exactly as weighted subset sums and convolve by event sweep."""
    atoms = {0: 1}
    v = [1]
    for j, main in enumerate(b[1:], 1):
        length = 1 << j
        v.append(interval_count(atoms, length))
        q = dict(atoms)
        for exponent, coefficient in atoms.items():
            q[exponent + main] = q.get(exponent + main, 0) + coefficient
        atoms = q
        v.append(interval_count(atoms, length))
    return v


def polynomial_product(a: list[int], b: list[int]) -> list[int]:
    out = [0] * (len(a) + len(b) - 1)
    for i, c in enumerate(a):
        for j, d in enumerate(b):
            out[i + j] += c * d
    return out


def check_recurrences(n: int = 2000) -> dict[str, int | bool]:
    a, b, g = construct(n)
    for j in range(1, n + 1):
        assert a[j] % 2 == 1
        assert abs(a[j]) <= (1 << j) - 1
        assert b[j] % 2 == 0 and b[j] > 0
        if j >= 3:
            assert abs(a[j]) <= (1 << j) - 3
            assert b[j] > sum(b[1:j])
        if j >= 5:
            assert b[j] == 5*b[j-1] - 10*b[j-2] + 12*b[j-3] - 8*b[j-4]
    for m in range(8, len(g)):
        assert g[m] == 5*g[m-2] - 10*g[m-4] + 12*g[m-6] - 8*g[m-8]
    q = [1, 0, -5, 0, 10, 0, -12, 0, 8]
    p = [0, 1, 2, -3, -8, 4, 16, -4, -8]
    coefficients = [0] + g
    for m in range(len(coefficients)):
        convolution = sum(q[j] * coefficients[m-j]
                          for j in range(min(m, len(q)-1)+1))
        assert convolution == (p[m] if m < len(p) else 0)
    assert polynomial_product([1, 0, -4, 0, 4], [1, 0, -1, 0, 2]) == q
    return {"blocks_checked": n, "exponents_checked": 2*n,
            "rational_gf_coefficient_identity": True,
            "integer_bounds_and_parity": True}


def generic_coding_tests(n: int = 10) -> int:
    """Test all 2^(n-2) sign choices a_3,...,a_n in {-1,1}.

    These are separate admissible controls in the general coding theorem.
    The checker uses the independent atom-and-interval implementation.
    """
    if n < 3 or n > 12:
        raise ValueError("generic test bound must be between 3 and 12")
    for mask in range(1 << (n - 2)):
        a = [2, 1, -3] + [1 if mask & (1 << j) else -1 for j in range(n-2)]
        b = [0]
        total = 0
        for j in range(1, n + 1):
            main = total + (1 << j) - 1 + a[j]
            b.append(main)
            total += main
        assert sparse_interval_checks(b) == predicted_counts(a)
    return 1 << (n-2)


def sign_statistics(n: int = 100000) -> dict[str, int | float]:
    # Streaming exact recurrence: do not evaluate cos(n*theta) numerically.
    previous, current = 2, 1
    positives = 0
    for j in range(1, n+1):
        positives += current > 0
        previous, current = current, current - 2*previous
    return {"indices": n, "positive": positives, "negative": n-positives,
            "positive_fraction": positives/n}


def write_data(output: Path) -> None:
    output.mkdir(parents=True, exist_ok=True)
    a, b, g = construct(128)
    with (output / "exponents_bfile.txt").open("w") as f:
        f.write("# m G_m, exact exponents, indices 1..256; no OEIS identifier assigned\n")
        for m, value in enumerate(g, 1):
            f.write(f"{m} {value}\n")
    long_a = trace_values(10000)
    v = predicted_counts(long_a)
    with (output / "coefficient_counts_bfile.txt").open("w") as f:
        f.write("# m nu_1(m), theorem-derived exact values, indices 0..20000\n")
        for m, value in enumerate(v):
            f.write(f"{m} {value}\n")
    with (output / "block_table.csv").open("w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(["n", "a_n", "G_2n_minus_1", "G_2n", "degree_P_2n",
                         "nu_1_2n_minus_1", "nu_1_2n", "overlap_deficit"])
        total = 0
        for j in range(1, 21):
            total += (1 << (j-1)) + b[j]
            odd = 2 if j == 1 else 4
            even = 4 if j == 1 else 4+4*(a[j] > 0)
            writer.writerow([j, a[j], 1 << (j-1), b[j], total, odd, even, 2*odd-even])
    with (output / "trace_bfile.txt").open("w") as f:
        f.write("# n a_n; exact trace sequence, indices 0..128\n")
        for n, value in enumerate(a):
            f.write(f"{n} {value}\n")


def main() -> None:
    if not __debug__:
        raise RuntimeError("Run without -O: this verifier uses assertions.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dense-blocks", type=int, default=14)
    parser.add_argument("--sparse-blocks", type=int, default=17)
    parser.add_argument("--numpy-dense", type=int, default=0,
                        help="optional independent int64 dense check through this many blocks")
    parser.add_argument("--generic-blocks", type=int, default=10)
    args = parser.parse_args()
    if not (2 <= args.dense_blocks <= 19 and 2 <= args.sparse_blocks <= 20 and 0 <= args.numpy_dense <= 20):
        parser.error("choose dense blocks 2..19, sparse blocks 2..20, and NumPy blocks 0..20 to bound memory use")
    ad, bd, gd = construct(args.dense_blocks)
    vd, degrees = dense_exact(gd)
    assert vd == predicted_counts(ad)
    asp, bsp, _ = construct(args.sparse_blocks)
    vs = sparse_interval_checks(bsp)
    assert vs == predicted_counts(asp)
    report: dict[str, object] = {
        "python": platform.python_version(),
        "run_time_utc": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "manuscript_date": "2026-09-19",
        "arithmetic": "exact integers; no floating-point sign decisions",
        "dense_python": {"blocks": args.dense_blocks, "factors": 2*args.dense_blocks,
                         "final_degree": degrees[-1], "passed": True},
        "sparse_event_sweep": {"blocks": args.sparse_blocks,
                               "factors": 2*args.sparse_blocks, "passed": True},
        "recurrences": check_recurrences(),
        "generic_control_words_checked": generic_coding_tests(args.generic_blocks),
        "sign_statistics": sign_statistics(),
        "all_checks_passed": True,
        "limitations": "Finite computations validate implementations, not nonperiodicity or natural boundaries. See the proofs."
    }
    if args.numpy_dense:
        an, bn, gn = construct(args.numpy_dense)
        vn, degree, max_coefficient = dense_numpy_exact(gn)
        assert vn == predicted_counts(an)
        report["dense_numpy_int64"] = {
            "blocks": args.numpy_dense, "factors": len(gn), "final_degree": degree,
            "maximum_coefficient": max_coefficient,
            "overflow_bound": f"sum of coefficients = 2^{len(gn)} < 2^63",
            "passed": True}
    write_data(ROOT / "data")
    path = ROOT / "data" / "verification.json"
    path.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
