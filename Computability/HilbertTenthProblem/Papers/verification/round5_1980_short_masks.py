#!/usr/bin/env python3
"""118 instructions by changing coefficient normalization and block widths.

This independent experimental successor preserves all round-four modules.
Its index construction and positive-domain proof are in
../1980/SHORT_MASKS_PROOF.md. The final histogram is verified symbolically;
that check is separate from the proof of the new index's universality.
"""
from __future__ import annotations

import json
from pathlib import Path
import sympy as sp

import round4_1980_operation_count as baseline
import round4_1980_packed_certificate as packed

HERE = Path(__file__).resolve().parent
OUT = HERE / "round5_1980_short_masks.json"
NU = 60
M = 5 ** NU
L = 5 ** 64
baseline.need(L == 625 * M and L > 4 * M and L >= 5 * M + 1,
              "fixed short-mask length satisfies the proof bounds")


def make_schedule():
    schedule = []
    for target, op, left, right in packed.SCHEDULE:
        if target in {"q3", "q16", "el", "elC2", "L1"}:
            continue
        if target in {"L2", "q4p1", "S3q4"}:
            left = "q2" if left == "q4" else left
            right = "q2" if right == "q4" else right
        if target == "lq2":
            right = "q"
        if target in {"Sq3", "Tq3"}:
            right = "q"
        if target == "b5m2q8":
            right = "q4"
        if target == "R20":
            right = L
        schedule.append((target, op, left, right))
        if target == "C4":
            schedule.extend([
                ("lC4", "*", "l", "C4"),
                ("bound_sum", "+", "e", "lC4"),
                ("L1", "+", "bound_sum", "al"),
            ])
    baseline.need(len(schedule) == 118, "118-operation short-mask schedule")
    return schedule


SCHEDULE = make_schedule()
EQUALITIES = list(packed.EQUALITIES)
EQUALITIES[0] = ("L1", "q")
EQUALITIES[5] = ("n", "q8")
NAMES = list(packed.NAMES)
SYM = dict(packed.SYM)


def source_residuals():
    s = SYM
    b, e, l, g, q, n = (s[v] for v in "b e l g q n".split())
    B = s["H"] * b ** 4
    C = 1 + s["x"] * B + g
    source = list(packed.source_residuals())
    source[0] = e + l * C ** 4 + s["al"] - q
    source[2] = s["la"] + q ** 2 - 1 - s["la"] * B
    source[4] = e + l * q - s["V"] - s["t"] * s["th"]
    source[5] = n - q ** 8
    S3 = (2 * e - s["Z"] * s["la"]) * C ** 4 + B * s["la"] * (1 + q ** 2)
    S = g + q * (e + l * q + q ** 2 * S3)
    Tp1 = q - (b - 1) * l + s["th"] * s["la"] * q + (B - 2) * q ** 4
    source[6] = s["r"] - S * (n ** 2 - n) - Tp1 * (n ** 2 - 1)
    source[-1] = s["ka"] - L - s["Delta"] * (s["a"] - 1)
    return source


def verify_certificate():
    env = dict(SYM)
    histogram = baseline.run_schedule(SCHEDULE, env)
    source = source_residuals()
    s = SYM
    correction = (s["la"] * source[3] - source[2]) * s["q"] * (s["n"] ** 2 - 1)
    signs = []
    for index, ((left, right), residual) in enumerate(zip(EQUALITIES, source)):
        actual = sp.expand(env[left] - env[right])
        if index == 6:
            baseline.need(sp.expand(actual - residual - correction) == 0,
                          "short-mask E7 triangular identity")
            signs.append(1)
        elif sp.expand(actual - residual) == 0:
            signs.append(1)
        elif sp.expand(actual + residual) == 0:
            signs.append(-1)
        else:
            raise AssertionError(f"residual mismatch at {index}: {left}={right}")
    used = {name for _, _, left, right in SCHEDULE for name in (left, right)
            if isinstance(name, str)}
    used |= {name for pair in EQUALITIES for name in pair}
    baseline.need(set(NAMES) <= used, "all source inputs used")
    baseline.need(len(EQUALITIES) == len(source) == 20, "20 residuals")
    baseline.need(sum(histogram.values()) == 118, "118-operation total")
    return {"status": "PASS", "operations": 118,
            "histogram": histogram,
            "additions": histogram["+"] + histogram["-"],
            "multiplications": histogram["*"],
            "unknowns": 32, "parameters": ["x", "Z", "V", "H"],
            "equations": 20, "residual_signs": signs,
            "exponent_numeral": str(L),
            "coefficient_witnesses": NU,
            "scope": "new normalized index; proof in SHORT_MASKS_PROOF.md",
            "optimality_claimed": False}


if __name__ == "__main__":
    result = verify_certificate()
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))
