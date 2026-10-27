"""Independent finite checks and matched-domain timings.

Run from any directory: python3 check_toeplitz.py [--benchmark]
Normal and optimized Python use the same explicit checks.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import random
import statistics
import sys
import time

from toeplitz_kernel import (Ring, boolean_action, convolve_scalar, dense_action,
                            dense_boolean_action,
                            direct_polynomial_diagonals, local_action,
                            packet_diagonals, strided_boolean_action, toeplitz_action)


def require_equal(a, b, label):
    if a != b:
        raise ArithmeticError(f"{label} mismatch: {a!r} != {b!r}")


def checks():
    rng = random.Random(20261026)
    digest = hashlib.sha256()
    counts = {"packet_cases": 0, "polynomial_diagonals": 0,
              "dense_actions": 0, "masked_actions": 0,
              "convolution_cases": 0, "invalid_inputs": 0,
              "boolean_actions": 0, "strided_actions": 0}
    zetas = [(0, 0), (1, 0), (-1, 0), (0, 1), (1, 1),
             (2, 0), (0, 2), (3, -5), (-19, 7)]
    cases = [(L, t, z, p) for L in (2, 4, 8)
             for t in range(-L, L) for z in zetas for p in (1, 2, 7, 17)]
    cases += [(16, rng.randrange(-16, 16),
               (rng.randrange(-(1 << 60), 1 << 60), rng.randrange(-(1 << 60), 1 << 60)),
               rng.choice((31, 64, 129))) for _ in range(40)]
    for L, t, z, p in cases:
        fast = packet_diagonals(L, t, z, p)
        oracle = direct_polynomial_diagonals(L, t, z, p)
        require_equal(fast, oracle, "cancelled polynomial")
        counts["packet_cases"] += 1
        counts["polynomial_diagonals"] += len(fast)
        vectors = [[(rng.randrange(2), 0) for _ in range(L)],
                   [(rng.randrange(-(1 << p), 1 << p), rng.randrange(-(1 << p), 1 << p))
                    for _ in range(L)]]
        for v in vectors:
            answer = toeplitz_action(fast, v, p)
            require_equal(answer, dense_action(oracle, v, p), "dense action")
            counts["dense_actions"] += 1
            digest.update(json.dumps(answer, separators=(",", ":")).encode())
        if counts["packet_cases"] % 7 == 0:
            cm = [bool(rng.randrange(2)) for _ in range(L)]
            rm = [bool(rng.randrange(2)) for _ in range(L)]
            vec = vectors[-1]
            want = dense_action(oracle, [v if k else (0, 0) for v, k in zip(vec, cm)], p)
            want = [v if k else (0, 0) for v, k in zip(want, rm)]
            require_equal(local_action(L, t, z, p, vec, cm, rm), want, "masked action")
            counts["masked_actions"] += 1
        bits = [x[0] for x in vectors[0]]
        rm = [bool(rng.randrange(2)) for _ in range(L)]
        require_equal(boolean_action(fast, bits, p, rm),
                      dense_boolean_action(oracle, bits, p, rm), "Boolean action")
        counts["boolean_actions"] += 1
        compact = [rng.randrange(2) for _ in range(L // 2)]
        full = [compact[y // 2] if y % 2 else 0 for y in range(L)]
        rows = [x % 2 == 0 for x in range(L)]
        require_equal(strided_boolean_action(fast, compact, p, 0, 1, 2),
                      dense_boolean_action(oracle, full, p, rows), "strided Boolean action")
        counts["strided_actions"] += 1
    for _ in range(350):
        p = rng.choice((1, 2, 3, 7, 16, 31, 65, 129))
        n, m = rng.randrange(1, 35), rng.randrange(1, 35)
        a = [rng.randrange(-(1 << (p + 8)), 1 << (p + 8)) for _ in range(n)]
        b = [rng.randrange(-(1 << (p + 8)), 1 << (p + 8)) for _ in range(m)]
        expected = [0] * (n + m - 1)
        for i, x in enumerate(a):
            for j, y in enumerate(b):
                expected[i + j] += x * y
        expected = [x % (1 << p) for x in expected]
        require_equal(convolve_scalar(a, b, p), expected, "packed convolution")
        counts["convolution_cases"] += 1
    invalid = [lambda: Ring(0), lambda: Ring(-1), lambda: Ring(True),
               lambda: Ring(3).inverse((2, 2)),
               lambda: packet_diagonals(3, 0, (0, 0), 4),
               lambda: packet_diagonals(4, 4, (0, 0), 4),
               lambda: packet_diagonals(4, 0, (0,), 4),
               lambda: toeplitz_action([], [], 3),
               lambda: toeplitz_action([(0, 0)], [(1, 0)] * 2, 3),
               lambda: local_action(4, 0, (0, 0), 4, [(0, 0)] * 3)]
    for f in invalid:
        try:
            f()
        except ValueError:
            counts["invalid_inputs"] += 1
        else:
            raise ArithmeticError("invalid input was accepted")
    return {"status": "PASS", "counts": counts, "digest": digest.hexdigest()}


def benchmark():
    rng = random.Random(20261027)
    results = []
    for L, p in ((32, 32), (64, 64), (128, 64), (256, 128), (512, 128)):
        t, z = 3, (1, 1)
        diag = packet_diagonals(L, t, z, p)
        v = [(rng.randrange(1 << p), rng.randrange(1 << p)) for _ in range(L)]
        expected = dense_action(diag, v, p)
        require_equal(toeplitz_action(diag, v, p), expected, "benchmark warmup")
        samples = {"dense": [], "convolution": [], "diagonal_preparation": []}
        for rep in range(5):
            order = [("dense", dense_action), ("convolution", toeplitz_action)]
            if rep % 2:
                order.reverse()
            for name, fn in order:
                start = time.perf_counter()
                actual = fn(diag, v, p)
                elapsed = time.perf_counter() - start
                require_equal(actual, expected, "timed action")
                samples[name].append(elapsed)
            start = time.perf_counter()
            actual = packet_diagonals(L, t, z, p)
            samples["diagonal_preparation"].append(time.perf_counter() - start)
            require_equal(actual, diag, "timed preparation")
        median = {k: statistics.median(v) for k, v in samples.items()}
        results.append({"L": L, "p": p, "t": t, "zeta": z,
                        "median_seconds": median, "samples_seconds": samples,
                        "action_ratio": median["dense"] / median["convolution"],
                        "including_preparation_ratio":
                        (median["dense"] + median["diagonal_preparation"]) /
                        (median["convolution"] + median["diagonal_preparation"]),
                        "output_sha256": hashlib.sha256(json.dumps(expected).encode()).hexdigest()})
    boolean_results = []
    for L, p in ((32, 32), (64, 64), (128, 64), (256, 128), (512, 128), (1024, 128)):
        diag = packet_diagonals(L, 3, (1, 1), p)
        row_mask = [x % 2 == 0 for x in range(L)]
        vector = [rng.randrange(2) if y % 2 else 0 for y in range(L)]
        expected = dense_boolean_action(diag, vector, p, row_mask)
        require_equal(boolean_action(diag, vector, p, row_mask), expected, "Boolean warmup")
        samples = {"dense_boolean_masked": [], "convolution_boolean_masked": [],
                   "strided_convolution_boolean_masked": []}
        compact = vector[1::2]
        def strided_control(diag, vec, bits, rows):
            return strided_boolean_action(diag, compact, bits, 0, 1, 2)
        for rep in range(5):
            order = [("dense_boolean_masked", dense_boolean_action),
                     ("convolution_boolean_masked", boolean_action),
                     ("strided_convolution_boolean_masked", strided_control)]
            if rep % 2:
                order.reverse()
            for name, fn in order:
                start = time.perf_counter()
                actual = fn(diag, vector, p, row_mask)
                samples[name].append(time.perf_counter() - start)
                require_equal(actual, expected, "timed Boolean action")
        median = {k: statistics.median(v) for k, v in samples.items()}
        boolean_results.append({"L": L, "p": p, "active_rows": sum(row_mask),
                                "nonzero_columns": sum(vector), "median_seconds": median,
                                "samples_seconds": samples,
                                "ratio": median["dense_boolean_masked"] /
                                median["convolution_boolean_masked"],
                                "strided_ratio": median["dense_boolean_masked"] /
                                median["strided_convolution_boolean_masked"],
                                "output_sha256": hashlib.sha256(json.dumps(expected).encode()).hexdigest()})
    return {"python": sys.version, "fixtures": results, "boolean_masked_fixtures": boolean_results,
            "scope": "exact vector actions in quadratic extension ring; Boolean control skips zero columns and masked rows; no SAT runtime claim"}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--benchmark", action="store_true")
    parser.add_argument("--output")
    args = parser.parse_args()
    result = benchmark() if args.benchmark else checks()
    data = json.dumps(result, indent=2) + "\n"
    if args.output:
        Path(args.output).write_text(data)
    print(data)
