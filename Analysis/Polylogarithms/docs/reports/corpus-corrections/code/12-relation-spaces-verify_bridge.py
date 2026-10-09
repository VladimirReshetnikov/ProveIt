#!/usr/bin/env python3
"""High-precision checks of both harmonic-number bridge parities.

Requires mpmath.  These checks supplement the analytic functional-equation
proof; no independence or transcendence conclusion is inferred.
"""

import argparse
import json
from pathlib import Path

import mpmath as mp


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dps", type=int, default=100)
    parser.add_argument("--output", type=Path, default=Path("data/bridge_checks.json"))
    args = parser.parse_args()
    mp.mp.dps = args.dps
    cases = [
        ("zeta", 1, 1, [1], [1, 2, 4]),
        ("beta", 4, -1, [0, 1, 0, -1], [1, 2, 3]),
        ("quadratic_mod_5", 5, 1, [0, 1, -1, -1, 1], [1, 2, 4]),
        ("quartic_mod_5", 5, -1, [0, 1, mp.j, -mp.j, -1], [1, 2, 3]),
    ]
    records = []
    worst = mp.mpf(0)
    for name, q, parity, values, orders in cases:
        def lfun(s):
            return mp.dirichlet(s, values)

        for k in orders:
            positive = mp.diff(lfun, k + 1) / lfun(k + 1)
            trivial = parity == (-1) ** k
            if trivial:
                negative = mp.diff(lfun, -k, 2) / (2 * mp.diff(lfun, -k))
                assert abs(lfun(-k)) < mp.mpf(10) ** (-args.dps + 10)
            else:
                negative = mp.diff(lfun, -k) / lfun(-k)
            expected = mp.euler + mp.log(2 * mp.pi / q) - mp.harmonic(k)
            residual = abs(positive + mp.conj(negative) - expected)
            assert residual < mp.mpf(10) ** (-args.dps + 12), (name, k, residual)
            worst = max(worst, residual)
            record = {
                "character": name,
                "conductor": q,
                "k": k,
                "trivial_zero_variant": trivial,
                "absolute_residual": mp.nstr(residual, 12),
            }
            if name == "quartic_mod_5":
                wrong_conjugation = abs(positive + negative - expected)
                assert wrong_conjugation > mp.mpf("0.01")
                record["residual_if_conjugation_omitted"] = mp.nstr(wrong_conjugation, 12)
            if trivial:
                wrong_factor = abs(positive + 2 * mp.conj(negative) - expected)
                assert wrong_factor > mp.mpf("0.01")
                record["residual_if_half_factor_omitted"] = mp.nstr(wrong_factor, 12)
            records.append(record)
    payload = {
        "mpmath_version": mp.__version__,
        "decimal_precision": args.dps,
        "case_count": len(records),
        "all_assertions_passed": True,
        "worst_absolute_residual": mp.nstr(worst, 12),
        "cases": records,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in payload.items() if key != "cases"}, indent=2))


if __name__ == "__main__":
    main()
