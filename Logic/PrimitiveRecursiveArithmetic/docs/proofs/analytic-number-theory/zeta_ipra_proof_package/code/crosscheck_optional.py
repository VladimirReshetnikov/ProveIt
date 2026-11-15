#!/usr/bin/env python3
"""Optional independent floating-point diagnostic, never a proof dependency.

Requires mpmath. The main evaluator and its exact finite checks use only
the Python standard library and do not import this module.
"""
from fractions import Fraction
import json
from pathlib import Path

import mpmath as mp


def main():
    root = Path(__file__).resolve().parents[1]
    enclosures = json.loads((root / "verification/enclosures.json").read_text())
    mp.mp.dps = 100

    def value(text):
        q = Fraction(text)
        return mp.mpf(q.numerator) / mp.mpf(q.denominator)

    reference = {
        "zeta_2": mp.zeta(2),
        "zeta_3": mp.zeta(3),
        "zeta_half": mp.zeta(mp.mpf(1) / 2),
        "euler_gamma": mp.euler,
        "zeta_half_plus_14i": mp.zeta(mp.mpc(mp.mpf(1) / 2, 14)),
    }
    results = []
    for name, target in reference.items():
        record = enclosures[name]
        radius = value(record["radius_l1"])
        error = abs(mp.re(target) - value(record["center_re"]))
        error += abs(mp.im(target) - value(record["center_im"]))
        results.append({
            "example": name,
            "inside_ball": bool(error <= radius),
            "comparison_error_over_radius": mp.nstr(error / radius, 12),
        })
    report = {
        "status": "PASS" if all(r["inside_ball"] for r in results) else "FAIL",
        "mpmath_version": mp.__version__,
        "decimal_precision": mp.mp.dps,
        "results": results,
        "limitation": (
            "Independent floating-point diagnostic; the enclosure proof uses "
            "exact rational balls and the manuscript, not mpmath."
        ),
    }
    output = root / "verification/numerical_crosscheck.json"
    output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))
    if report["status"] != "PASS":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
