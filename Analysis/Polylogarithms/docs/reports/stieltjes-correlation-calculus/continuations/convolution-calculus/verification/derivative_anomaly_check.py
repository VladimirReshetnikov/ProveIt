#!/usr/bin/env python3
"""Independent raw-cutoff diagnostics for the k=1 derivative anomaly.

These are arbitrary-precision numerical checks, not interval certificates.
The article contains the proof. The first cutoff-error coefficient is
computed from the two endpoint Taylor expansions.

Run:
    python derivative_anomaly_check.py
Requires mpmath.
"""
import argparse
import json
from pathlib import Path
import platform
import mpmath as mp


def cutoff_value(a, eps):
    """Subtract all divergent terms at x=0+ and x=a- separately."""
    pa = mp.digamma(a)
    p1a = mp.polygamma(1, a)
    cut = mp.sqrt(eps)
    left_zero = mp.quad(
        lambda x: mp.digamma(x) * mp.polygamma(1, a - x),
        [eps, cut, a / 4, a / 2],
    )
    # Use y=a-x as the integration variable near the other singularity.
    # This avoids losing digits when a-x is formed from nearly equal numbers.
    left_a = mp.quad(
        lambda y: mp.digamma(a - y) * mp.polygamma(1, y),
        [eps, cut, a / 4, a / 2],
    )
    right = mp.quad(
        lambda x: mp.digamma(x) * mp.polygamma(1, 1 + a - x),
        [a, (a + 1) / 2, 1],
    )
    return left_zero + left_a + right - pa / eps - 2 * p1a * mp.log(eps)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path,
        default=Path(__file__).with_name("results_derivative_anomaly.json"))
    args = parser.parse_args()
    mp.mp.dps = 65
    records = []
    for a_text in ["0.5", "0.37"]:
        a = mp.mpf(a_text)
        expected = 2 * mp.diff(lambda s: mp.zeta(s, a), mp.mpf(2)) + mp.zeta(2, a)
        first_error_coefficient = (mp.euler * mp.polygamma(1, a)
            - mp.mpf("1.5") * mp.polygamma(2, a)
            - mp.zeta(2) * mp.digamma(a))
        for exponent in [6, 12, 18]:
            eps = mp.mpf(10) ** (-exponent)
            value = cutoff_value(a, eps)
            corrected = value - first_error_coefficient * eps
            assert abs(corrected - expected) < 1000 * eps ** 2
            records.append(
                {
                    "a": a_text,
                    "epsilon": str(eps),
                    "cutoff_value": mp.nstr(value, 50),
                    "predicted_limit": mp.nstr(expected, 50),
                    "difference": mp.nstr(value - expected, 20),
                    "difference_over_epsilon": mp.nstr((value - expected) / eps, 20),
                    "predicted_first_error_coefficient": mp.nstr(first_error_coefficient, 35),
                    "first_order_corrected_value": mp.nstr(corrected, 50),
                    "first_order_corrected_difference": mp.nstr(corrected - expected, 20),
                }
            )
    result = {"status": "passed",
        "verification_kind": "arbitrary-precision diagnostics, not interval certificates",
        "decimal_precision": mp.mp.dps,
        "python_version": platform.python_version(),
        "mpmath_version": mp.__version__, "records": records}
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(str(args.output))


if __name__ == "__main__":
    main()

