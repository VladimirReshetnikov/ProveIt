#!/usr/bin/env python3
"""Reproduce exact tests and write JSON/CSV reports. No third-party packages."""
import csv
import json
import platform
import sys
import time
from decimal import Decimal, localcontext
from pathlib import Path
from stabilization import (valuation, decimal_profile, decimal_increment,
    decimal_onset, minimum_failure, minimum_failure_spec, failure_density,
    radix_profile, modular_certificate, decimal_idempotent_mod)


def run() -> dict:
    started = time.perf_counter()
    counts = {}
    a0 = 3 * 2**99 + 1
    assert a0 == 1901475900342344102245054808065
    assert minimum_failure(3) == a0
    assert valuation(a0, 5) == 1
    assert valuation(a0*a0 - 1, 2) - 1 == 99
    assert decimal_increment(a0, 3) == 2
    assert decimal_onset(a0) == 4
    assert a0*a0 + 1 < 5**99
    primary = []
    for b in range(2, 9):
        s = decimal_profile(a0, b)
        cert = modular_certificate(a0, 10, b, s)
        primary.append({"b": b, "S": s, **cert})
    counts["primary_modular_certificates"] = len(primary)

    ntests = 0
    for a in range(2, 2001):
        for b in range(2, 7):
            if a % 10 == 0:
                continue
            s = decimal_profile(a, b)
            assert radix_profile(a, 10, b) == s
            modular_certificate(a, 10, b, s)
            ntests += 1
    counts["small_decimal_modular_certificates"] = ntests

    ntests = 0
    for k in [1, 2, 4, 30, 98, 99, 100, 101, 998, 999, 1000]:
        a = 5**k + 1
        for b in range(2, 7):
            s = decimal_profile(a, b)
            assert s == min(10**b, b + k)
            modular_certificate(a, 10, b, s)
            ntests += 1
    for m in range(2, 5):
        k = 10**m - m + 1
        a = 5**k + 1
        assert decimal_increment(a, m + 1) == 2
        assert decimal_onset(a) == m + 2
        for b in [m, m + 1, m + 2]:
            modular_certificate(a, 10, b, decimal_profile(a, b))
            ntests += 1
    counts["delayed_family_modular_certificates"] = ntests

    # All 20 residue classes, independently enumerating candidates j*2^K +/- 1.
    ntests = 0
    for k in range(99, 199):
        candidates = sorted(j * 2**k + s for j in range(1, 5) for s in [-1, 1])
        least = next(a for a in candidates if a % 5 == 0 and a % 25 != 0)
        r = k % 20
        spec = ({0: (4, 1), 9: (3, -1), 10: (4, -1), 19: (3, 1)}.get(r)
                or [(1, -1), (2, 1), (1, 1), (2, -1)][r % 4])
        assert least == spec[0] * 2**k + spec[1]
        assert valuation(least*least - 1, 2) - 1 == k + valuation(spec[0], 2)
        assert (4 * 2**k + 1)**2 + 1 < 5**k
        ntests += 1
    counts["minimum_table_residue_tests"] = ntests

    minima = []
    for b in range(3, 6):
        a = minimum_failure(b)
        k, j, sign = minimum_failure_spec(b)
        assert decimal_increment(a, b) == 2 + valuation(j, 2)
        assert decimal_onset(a) == b + 1
        for n in [b - 1, b]:
            modular_certificate(a, 10, n, decimal_profile(a, n))
        minima.append({"b": b, "K": k, "j": j, "sign": sign,
                       "increment": decimal_increment(a, b)})
    counts["stage_minimum_modular_certificates"] = 2 * len(minima)

    ntests, skipped = 0, 0
    for base in range(2, 36):
        for a in range(2, 102):
            for n in range(1, 5):
                s = radix_profile(a, base, n)
                if s > 160:
                    skipped += 1  # These would demand needlessly huge moduli.
                    continue
                modular_certificate(a, base, n, s)
                ntests += 1
    counts["general_radix_modular_certificates"] = ntests
    counts["general_radix_cases_skipped_due_to_modulus_cap"] = skipped

    ntests = 0
    for a in range(2, 82):
        for n in range(2, 5):
            for lag in [2, 3]:
                if a % 10 == 0:
                    continue
                s = decimal_profile(a, n)
                modular_certificate(a, 10, n, s, lag=lag)
                ntests += 1
    counts["nonconsecutive_modular_certificates"] = ntests

    # Radix 14, base 2 has an order-3 obstruction; step 2 removes it.
    for n in range(1, 5):
        assert radix_profile(2, 14, n) == 0
        s = radix_profile(2, 14, n, lag=2)
        assert s == n + 1
        modular_certificate(2, 14, n, s, lag=2)
    counts["period_two_radix_certificates"] = 4

    for a in [2, 3, 5, 10, a0]:
        for digits in [1, 2, 8, 30]:
            z = decimal_idempotent_mod(a, digits)
            assert (z*z - z) % 10**digits == 0
            n = max(2, digits + 2)
            assert pow(a, 10**n, 10**digits) == z
    counts["idempotent_modular_tests"] = 20

    density = failure_density(3)
    with localcontext() as ctx:
        ctx.prec = 45
        density_decimal = str(Decimal(density.numerator) / Decimal(density.denominator))
    return {"status": "PASS", "python": platform.python_version(),
            "elapsed_seconds": round(time.perf_counter() - started, 3),
            "least_counterexample": str(a0), "counts": counts,
            "primary_certificates": primary, "stage_minima": minima,
            "failure_density_b3": {"numerator": str(density.numerator),
               "denominator": str(density.denominator), "decimal": density_decimal},
            "scope": "Exact arithmetic regression and modular checks; not a proof-assistant formalization."}


if __name__ == "__main__":
    outdir = Path(__file__).resolve().parents[1] / "data"
    outdir.mkdir(exist_ok=True)
    report = run()
    (outdir / "verification.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    with (outdir / "primary_certificates.csv").open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=["b", "S", "valuation", "first_nonzero_digit"])
        w.writeheader()
        w.writerows(report["primary_certificates"])
    print(json.dumps(report, indent=2))
