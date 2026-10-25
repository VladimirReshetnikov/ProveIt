#!/usr/bin/env python3
"""Exact finite diagnostics for the proved factorial-rounding lemma.

These checks do not establish the unbounded theorem, which is proved in
BOOTSTRAP_PROOF.md. They independently exercise the sharp threshold, the
completeness margin, and the exceptional F=0 coefficient issue.
"""

from math import comb, factorial
import json


def require(condition, message):
    if not condition:
        raise ValueError(message)


def rounded_fixed_point(t, f):
    b = comb(f * f + t, t)
    v = (f * f + 1) ** t
    return 2 * abs(f * b - v) < b


def main():
    scans = []
    for t in range(2, 9):
        h = factorial(t)
        roots = [f for f in range(-2, h + 2) if rounded_fixed_point(t, f)]
        expected = {2: [1, 2], 3: [5, 6]}.get(t, [h])
        require(roots == expected, f"wrong exact fixed points at t={t}")
        scans.append({"t": t, "interval": [-2, h + 1], "fixed_points": roots})

    margins = []
    for t in (4, 5, 8, 16, 17, 24, 32, 64):
        h = factorial(t)
        b = comb(h * h + t, t)
        v = (h * h + 1) ** t
        s = h * b - v
        a = t * (t - 1) // 2
        require(0 < s, f"wrong canonical slack sign at t={t}")
        require(h * s < a * b, f"failed factorial margin at t={t}")
        if t >= 16:
            require(32 * s < b, f"failed common-norm margin at t={t}")
        margins.append({"t": t, "strict_error_below_a_over_factorial": True,
                        "strict_error_below_one_over_32": 32 * s < b})

    # An inherited estimate needs m>=1; m=F^2=0 is a real exception.
    require(comb(16, 1) > (0 + 1) ** 16,
            "the expected F=0 coefficient counterexample disappeared")
    # Exact uniform replacement used by the new proof in that exception.
    for t in range(16, 100):
        require(32 * 2 ** (t + 1) < 3 ** (t + 1),
                f"failed zero-factorial short-remainder margin at t={t}")

    print(json.dumps({"status": "PASS", "scope": "finite exact diagnostics",
                      "unbounded_proof": "BOOTSTRAP_PROOF.md",
                      "threshold_scans": scans, "canonical_margins": margins,
                      "f_zero_counterexample_checked": True,
                      "f_zero_repair_t_interval": [16, 99]}, indent=2))


if __name__ == "__main__":
    main()
