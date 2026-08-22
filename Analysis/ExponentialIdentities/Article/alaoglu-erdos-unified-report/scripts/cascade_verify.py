#!/usr/bin/env python3
"""Independent small-N Bareiss checks for cascade_experiments.py."""

import importlib.util
import sys
from pathlib import Path

sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location(
    "ce", Path(__file__).with_name("cascade_experiments.py")
)
ce = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ce)


def bareiss(a):
    a = [row[:] for row in a]
    n = len(a)
    sign = 1
    previous = 1
    for k in range(n - 1):
        pivot_row = next((i for i in range(k, n) if a[i][k]), None)
        if pivot_row is None:
            return 0
        if pivot_row != k:
            a[k], a[pivot_row] = a[pivot_row], a[k]
            sign = -sign
        pivot = a[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                numerator = a[i][j] * pivot - a[i][k] * a[k][j]
                assert numerator % previous == 0
                a[i][j] = numerator // previous
            a[i][k] = 0
        previous = pivot
    return sign * a[-1][-1]


for M, A in [(5, 7), (5, 11), (11, 5), (13, 17)]:
    for T in (4, 8, 12, 20, 25):
        d = ce.block_data(T, M, A)
        if d["N"] > 12:
            continue
        matrix = []
        for k, nk in enumerate(d["n"]):
            m = 2**nk * M**k
            a = 3**nk * A**k
            matrix.append([m**u * a**v for u, v in d["pairs"]])
        determinant = bareiss(matrix)
        assert determinant
        for p in (2, 3):
            weights = [uv[0 if p == 2 else 1] for uv in d["pairs"]]
            tau = ce.tropical_min(d["n"], weights)
            modular, _ = ce.exact_det_valuation(d, p, tau)
            direct = ce.v_p(determinant, p)
            assert modular == direct, (M, A, T, p, modular, direct)
        print("verified", M, A, T, d["N"])
