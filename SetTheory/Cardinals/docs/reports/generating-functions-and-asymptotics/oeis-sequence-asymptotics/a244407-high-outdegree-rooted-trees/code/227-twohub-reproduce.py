#!/usr/bin/env python3
"""Run bounded exact tests and optional non-certified numerical diagnostics."""
import argparse
import hashlib
import json
from math import isfinite
from pathlib import Path
import sys
from time import perf_counter

from exact import (MAX_BOUNDED_N, MAX_COEFFICIENT, MAX_DEGREE, MAX_ORBIT_N,
                   basic_series, bounded_checks, bounded_trees, cap,
                   canonical_trees, defect_series, defect_diagnostics, moment_diagnostics,
                   orbit_checks, require)

DATA = Path(__file__).resolve().parent.parent / "data"
PROFILES = {
    "quick": {"bounded_n": 32, "degree_cap": 16, "orbit_n": 8, "coefficient_n": 160},
    "full": {"bounded_n": 80, "degree_cap": 32, "orbit_n": 11, "coefficient_n": 800},
    "caps": {"bounded_n": 96, "degree_cap": 32, "orbit_n": 12, "coefficient_n": 1000},
}


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def expect_failure(function, description):
    try:
        function()
    except RuntimeError:
        return
    raise RuntimeError(f"guard failed to reject {description}")


def check_guards():
    expect_failure(lambda: require(False, "intentional require self-test"), "false require")
    expect_failure(lambda: basic_series(MAX_COEFFICIENT + 1), "excess coefficient cap")
    expect_failure(lambda: bounded_trees(MAX_BOUNDED_N + 1, 1), "excess bounded N")
    expect_failure(lambda: bounded_trees(4, MAX_DEGREE + 1), "excess degree cap")
    expect_failure(lambda: canonical_trees(MAX_ORBIT_N + 1), "excess orbit N")
    expect_failure(lambda: cap(True, 0, 4, "test"), "boolean cap")
    return 6


def check_smallest_endpoints():
    series = basic_series(1)
    defect = defect_series(series, 1)
    moments = moment_diagnostics(series, 1, maximum_order=6)
    correction = defect_diagnostics(defect, 1)
    require(series["F"] == [1, 2] and defect["B"] == [1, 7],
            "smallest coefficient endpoint failed")
    for family in ("depth_falling_moments", "decoration_integer_moments"):
        for samples in moments[family].values():
            require(len(samples) == 1 and samples[0]["m"] == 1,
                    "smallest moment endpoint includes an invalid sample")
            require(isfinite(samples[0]["ratio_to_leading_equivalent"]),
                    "smallest moment endpoint is nonfinite")
    require(len(correction["samples"]) == 1 and correction["samples"][0]["r"] == 1,
            "smallest defect endpoint includes an invalid sample")
    require(isfinite(correction["samples"][0]["ratio_to_leading_equivalent"]),
            "smallest defect endpoint is nonfinite")
    return {"final_index": 1, "moment_orders": 6,
            "moment_diagnostics": "passed", "defect_diagnostics": "passed"}


def check_fixture(series, defect):
    path = DATA / "exact_coefficients.json"
    fixture = json.loads(path.read_text())
    require(fixture["kind"] == "exact-generated", "incorrect coefficient fixture kind")
    n = fixture["final_index"]
    require(n <= len(defect["B"]) - 1, "fixture exceeds computed defect series")
    count = 0
    for key in ("H", "G", "F", "J2"):
        require(fixture["coefficients"][key] == series[key][:n + 1], f"fixture mismatch: {key}")
        count += n + 1
    require(fixture["coefficients"]["r"] == series["r"][:n + 3], "fixture mismatch: r")
    require(fixture["coefficients"]["B"] == defect["B"][:n + 1], "fixture mismatch: B")
    return {"coefficients_checked": count + (n + 3) + (n + 1), "sha256": sha256(path)}


def check_oeis(series):
    path = DATA / "oeis_samples.json"
    data = json.loads(path.read_text())
    require(data["kind"] == "externally-observed-samples", "OEIS data is not tagged external")
    results = {}
    for entry in data["sequences"]:
        accession, start = entry["accession"], entry["start_index"]
        for index, actual in enumerate(entry["terms"], start):
            if accession == "A244407":
                expected = series["F"][index - 1]
            elif accession == "A244410":
                expected = 1 if index == 0 else series["F"][index] - 1
            else:
                raise RuntimeError(f"unexpected OEIS accession {accession}")
            require(actual == expected, f"external sample mismatch: {accession}({index})")
        results[accession] = {"start_index": start, "terms_checked": len(entry["terms"]),
                              "source_url": entry["source_url"]}
    results["sha256"] = sha256(path)
    return results


def run(profile, numerical=False, order=3, precision=60):
    settings = PROFILES[profile]
    guards = check_guards()
    endpoints = check_smallest_endpoints()
    series = basic_series(settings["coefficient_n"])
    fixture_n = json.loads((DATA / "exact_coefficients.json").read_text())["final_index"]
    require(fixture_n <= settings["coefficient_n"], "coefficient profile is shorter than fixture")
    defect = defect_series(series)
    fixtures = check_fixture(series, defect)
    external = check_oeis(series)
    bounded_result, bounded, component_table = bounded_checks(
        settings["bounded_n"], settings["degree_cap"], series, defect)
    orbits = orbit_checks(settings["orbit_n"], series, defect, bounded, component_table)
    moments = moment_diagnostics(series, settings["coefficient_n"])
    output = {
        "status": "all requested finite checks passed",
        "profile": profile,
        "settings": settings,
        "limits": {"coefficient_n": MAX_COEFFICIENT, "bounded_n": MAX_BOUNDED_N,
                   "degree_cap": MAX_DEGREE, "orbit_n": MAX_ORBIT_N},
        "guard_checks": guards,
        "smallest_endpoint_checks": endpoints,
        "exact_generated_fixture": fixtures,
        "external_oeis_samples": external,
        "bounded_outdegree_checks": bounded_result,
        "canonical_colored_orbit_checks": orbits,
        "initial_coefficients": {key: series[key][:16] for key in ("r", "H", "G", "F", "J2")},
        "initial_defect_coefficients": defect["B"][:16],
        "moment_diagnostics": moments,
        "defect_diagnostics": defect_diagnostics(defect, settings["coefficient_n"]),
        "scope": "Finite tests and diagnostics only. Neither arbitrary-order proof nor interval certification is claimed.",
    }
    if numerical:
        try:
            from numerics import numerical_diagnostics
        except ImportError as exc:
            raise RuntimeError("--numerics requires mpmath; see code/README.md") from exc
        output["numerical_diagnostics"] = numerical_diagnostics(order=order, precision=precision)
    return output


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--quick", action="store_true", help="N<=32; canonical N<=8; moments m<=160 (default)")
    group.add_argument("--full", action="store_true", help="N<=80; canonical N<=11; moments m<=800")
    group.add_argument("--caps", action="store_true", help="exercise all hard exact caps: N<=96, canonical N<=12, moments m<=1000")
    parser.add_argument("--numerics", action="store_true", help="include optional mpmath Puiseux/Gamma/inverse diagnostics")
    parser.add_argument("--order", type=int, default=3, help="numerical expansion order (finite cap 8)")
    parser.add_argument("--precision", type=int, default=60, help="numerical working decimal precision")
    args = parser.parse_args()
    if not args.numerics and (args.order != 3 or args.precision != 60):
        parser.error("--order and --precision apply only with --numerics")
    started = perf_counter()
    try:
        profile = "caps" if args.caps else ("full" if args.full else "quick")
        result = run(profile, args.numerics, args.order, args.precision)
    except (RuntimeError, ValueError) as exc:
        print(json.dumps({"status": "failed", "error": str(exc)}, sort_keys=True))
        return 1
    print(json.dumps(result, indent=2, sort_keys=True))
    print(f"Elapsed wall time: {perf_counter() - started:.3f} seconds", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
