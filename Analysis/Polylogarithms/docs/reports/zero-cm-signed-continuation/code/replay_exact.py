#!/usr/bin/env python3
"""Reconstruct all finite proof certificates with the Python standard library.

No network, numerical special-function library, or stored numerical values
are used. Stored rational proof objects are compared with fresh calculations.
The Gaussian intervals prove proximity; they do not prove the identities.
Run without -O, because the individual proof programs use assertions.
"""
import contextlib
import io
import json
from pathlib import Path
import platform
import tempfile

if not __debug__:
    raise RuntimeError("Run the certificate replay without Python -O.")

import certify_gamma_saddle as gamma
import interval_certificate as gaussian
import verify_lerch_bifurcations as lerch

ROOT = Path(__file__).resolve().parents[1]
RESULTS = ROOT / "results"


def read(name):
    return json.loads((RESULTS / name).read_text())


def without_runtime(report):
    return {key: value for key, value in report.items()
            if key != "elapsed_seconds"}


def main():
    checks = []
    with contextlib.redirect_stdout(io.StringIO()):
        actual = gamma.run()
    if actual != read("gamma_saddle_certificate.json"):
        raise AssertionError("Reflected inequality certificate differs.")
    checks.append({"name": "reflected_inequality", "status": "passed",
                   "exact_intervals": actual["intervals_checked"],
                   "lower_bound": [actual["global_D_lower_numerator"],
                                   actual["global_D_lower_denominator"]]})
    print("PASS: all 112 exact reflected-inequality intervals.")

    actual = lerch.verify()
    if actual != read("lerch_endpoint_certificates.json"):
        raise AssertionError("Lerch endpoint sign certificate differs.")
    checks.append({"name": "lerch_endpoint_signs", "status": "passed",
                   "exact_signs": len(actual["rows"])})
    print("PASS: all 9 exact Lerch endpoint signs.")

    with tempfile.TemporaryDirectory(prefix="polylog_exact_") as scratch:
        gaussian.HERE = Path(scratch)
        for N, scheme, name, exponent in [
            (1100, "source", "s6_s8_interval_certificate.json", 330),
            (1200, "direct", "s6_s8_direct_interval_certificate.json", 355),
        ]:
            with contextlib.redirect_stdout(io.StringIO()):
                gaussian.run(N=N, gaussian_bound=scheme)
            actual = json.loads((gaussian.HERE / name).read_text())
            if without_runtime(actual) != without_runtime(read(name)):
                raise AssertionError(f"Gaussian {scheme} certificate differs.")
            checks.append({"name": f"gaussian_proximity_{scheme}",
                           "status": "passed", "Euler_terms": N,
                           "normalized_bound_exponent": exponent,
                           "identities_proved": False})
            print(f"PASS: exact S6 and S8 {scheme} enclosures within 10^-{exponent}.")

    result = {
        "status": "all finite proof certificates independently reconstructed",
        "python": platform.python_version(),
        "arithmetic": "standard-library integers and rational intervals",
        "stored_certificate_comparison": "exact; excludes elapsed_seconds only",
        "checks": checks,
        "scope": ("Analytic coverage and tail bounds are proved in the article. "
                  "S6 and S8 identities remain conjectural."),
    }
    (RESULTS / "replay_summary.json").write_text(
        json.dumps(result, indent=2) + "\n")
    print("All certificate replays passed.")


if __name__ == "__main__":
    main()

